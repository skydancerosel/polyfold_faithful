import Polyfold.Chapter12.RestrictionLocalIso
import Polyfold.Chapter12.OrientationGermSquare
import Polyfold.Chapter12.ChartTransportCommute
import Polyfold.Chapter11.FaceIntersectionCounterexample

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.2,
Definition 6.2.1 and the paragraph before it (pp. 239–240), §6.6 (the paragraph before
Proposition 6.6.1 and Definition 6.6.2), and Chapter 12, §12.5, p. 592.

# The orientation sets `Or_x^f` made with local sc⁺-sections

## The text, paraphrased

For an sc-Fredholm section `f` of a strong bundle `P : Y → X` over a tame M-polyfold and a
smooth point `x`, the text chooses "a locally defined sc⁺-section `s`" with `s(x) = f(x)`, for
instance in a strong bundle chart around `x`, and forms the linearization `(f − s)'(x)`.  These
linearizations make up the convex set `Lin(f, x)`; `DET(f, x)` is a line bundle over it and
`Or_x^f` is the set of its two orientations.  §12.5 uses the same sets for the section functor
of a strong bundle over an ep-groupoid.

## What is formalized

`Lin(f, x)` and `Or_x^f` are made with the sc⁺-sections over an open subset of the base domain
of a chart, and the set does not depend on the subset.  No sc-smooth bump functions and no
sc⁺-sections over all of `X` are assumed.

* `StrongBundle.Dom B`: a *domain*, a nonempty open subset `W` of the base inside the base
  domain of a chart of the atlas.  The restriction `P|W` (`Dom.bundle`) has a chart over its
  whole base (`Dom.exists_chart_univ`), hence sc⁺-sections through all smooth fibre points
  (`Dom.hasSections`); `W` is tame if `X` is (`Dom.isTame`) and `f|W` (`Dom.sec`) has tame germ
  data (`Dom.isFredholm`).  `Dom.transport` is the transport of orientations of `f|W` along
  sc-smooth paths in `W`.  Domains: `Dom.ofChart`, `Dom.inter`, `Dom.restrict`, and the chosen
  domain `StrongBundle.domAt x` at a point.
* `Dom.Or hf x hx hs`: the set `Or_x^{f|W}` for `x ∈ W` smooth; it has two elements
  (`Dom.exists_two_or`).
* `Dom.iso D D'`: the identification of `P|W` and `P|W'` over `W ∩ W'`, with
  `Dom.sec_eqOn_iso`, the germ of the composite (`Dom.iso_comp_germ`) and of `Dom.iso D D`
  (`Dom.iso_self_germ`).
* `Dom.compare`: **the comparison map** `Or_x^{f|W'} ≃ Or_x^{f|W}` for `x ∈ W ∩ W'`; it is the
  identity for `W' = W` (`Dom.compare_self`), satisfies the cocycle condition
  (`Dom.compare_trans`) and `Dom.compare_symm`.
* `OrxLoc hf x hs`: **the local orientation set** `Or_x^f`, read in the chosen domain at `x`; it
  has two elements (`exists_two_orxLoc`).  `Dom.toLoc`: its identification with `Or_x^{f|W}`
  for every domain `W ∋ x`, compatible with the comparison maps (`Dom.toLoc_compare`).
* `Dom.compare_transport`: for domains `W ⊆ W'` the comparison maps intertwine the transport of
  `f|W` along an sc-smooth path in `W` and the transport of `f|W'` along the same path.
* `Dom.linSet_restrictIso`: if `P` has sc⁺-sections through all smooth fibre points, then for a
  chart point `p` at `x` with base domain inside `W`, `Lin(f|W, x)` read in the carried chart
  point is `Lin(f, x)` read in `p`.
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

/-! ### Domains -/

/-- **A domain of a strong bundle**: a nonempty open subset of the base which lies in the base
domain of a chart of the atlas. -/
structure StrongBundle.Dom (B : StrongBundle PX P) where
  /-- The open set. -/
  carrier : Set X
  isOpen : IsOpen carrier
  nonempty : carrier.Nonempty
  exists_chart : ∃ c ∈ B.atlas.charts, carrier ⊆ c.φ.source

namespace StrongBundle.Dom

instance instNonempty (D : B.Dom) : Nonempty D.carrier := D.nonempty.to_subtype

instance instParacompact (D : B.Dom) : ParacompactSpace D.carrier :=
  PX.paracompactSpace_subtype D.carrier

instance instParacompactPullback (D : B.Dom) :
    ParacompactSpace (pullbackSpace P (Subtype.val : D.carrier → X)) :=
  paracompactSpace_pullbackSpace (f := (Subtype.val : D.carrier → X))
    (PX.restrictOpen D.isOpen) B

instance instParacompactRnProd (D : B.Dom) (n : ℕ) :
    ParacompactSpace ((Fin n → ℝ) × D.carrier) :=
  paracompactSpace_rn_prod (PX.restrictOpen D.isOpen) n

instance instParacompactRnPullback (D : B.Dom) (n : ℕ) :
    ParacompactSpace (pullbackSpace (pullbackProj P (Subtype.val : D.carrier → X))
      (Prod.snd : (Fin n → ℝ) × D.carrier → D.carrier)) :=
  paracompactSpace_rn_pullback (B.restrictOpen D.isOpen) n

instance instParacompactRnRnProd (D : B.Dom) (k n : ℕ) :
    ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × D.carrier)) :=
  paracompactSpace_rn_rn_prod (PX.restrictOpen D.isOpen) k n

instance instParacompactRnRnPullback (D : B.Dom) (k n : ℕ) :
    ParacompactSpace (pullbackSpace
      (pullbackProj (pullbackProj P (Subtype.val : D.carrier → X))
        (Prod.snd : (Fin n → ℝ) × D.carrier → D.carrier))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × D.carrier) → (Fin n → ℝ) × D.carrier)) :=
  paracompactSpace_rn_rn_pullback (B.restrictOpen D.isOpen) k n

variable (D D' D'' : B.Dom)

/-- **The restriction `P|W` of the bundle to a domain `W`.** -/
abbrev bundle : StrongBundle (PX.restrictOpen D.isOpen)
    (pullbackProj P (Subtype.val : D.carrier → X)) :=
  B.restrictOpen D.isOpen

/-- **The restriction `f|W` of a section to a domain `W`.** -/
abbrev sec (f : X → Y) (hfs : IsSection P f) :
    D.carrier → pullbackSpace P (Subtype.val : D.carrier → X) :=
  restrictSection P D.carrier f hfs

/-- A domain of a tame M-polyfold is tame. -/
theorem isTame (hX : PX.IsTame) : (PX.restrictOpen D.isOpen).IsTame :=
  MPolyfold.isTame_restrictOpen PX D.isOpen hX

/-- **The restriction of the bundle to a domain has a chart of its atlas over its whole base.** -/
theorem exists_chart_univ : ∃ c ∈ D.bundle.atlas.charts, c.φ.source = univ :=
  let ⟨_, hc, hsub⟩ := D.exists_chart
  StrongBundle.exists_chart_source_eq_univ_restrictOpen_of_subset hc D.isOpen hsub

/-- **Over a domain there are sc⁺-sections through all smooth fibre points** (in the chart over
the whole base). -/
theorem hasSections : D.bundle.HasScPlusSectionsThrough :=
  D.exists_chart_univ.elim fun _ h => StrongBundle.hasScPlusSectionsThrough_of_chart h.1 h.2

/-- **The restriction of an sc-Fredholm section with tame germ data to a domain** has tame germ
data. -/
theorem isFredholm (hf : B.IsScFredholmSectionTame f) :
    D.bundle.IsScFredholmSectionTame (D.sec f hf.isScSmooth.1) :=
  hf.restrictOpen D.isOpen

variable {D} in
/-- A point of a domain which is smooth in `X` is a smooth point of the domain. -/
theorem mem_smoothSet {x : X} (hx : x ∈ D.carrier) (hs : x ∈ PX.smoothSet) :
    (⟨x, hx⟩ : D.carrier) ∈ (PX.restrictOpen D.isOpen).smoothSet :=
  (MPolyfold.mem_smoothSet_restrictOpen_iff D.isOpen ⟨x, hx⟩).2 hs

/-- **The transport of orientations over a domain**: the transport of the orientations of `f|W`
along sc-smooth paths in `W`, made in the chart of `P|W` over `W`. -/
def transport (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f) :
    LocalTransport (PX.restrictOpen D.isOpen) (fun w hs =>
      Orx (D.sec f hf.isScSmooth.1) (D.isFredholm hf).toIsScFredholmSection w hs) :=
  orLocalTransportOfChart (D.isTame hX) D.exists_chart_univ (D.isFredholm hf) D.hasSections

/-- **`Or_x^{f|W}`**: the orientations of `DET(f|W, x)` for a domain `W` and a smooth `x ∈ W`;
the linearizations are those of `f|W − s` for the sc⁺-sections `s` of `P|W`. -/
abbrev Or (hf : B.IsScFredholmSectionTame f) (x : X) (hx : x ∈ D.carrier)
    (hs : x ∈ PX.smoothSet) : Type _ :=
  Orx (D.sec f hf.isScSmooth.1) (D.isFredholm hf).toIsScFredholmSection ⟨x, hx⟩
    (mem_smoothSet hx hs)

/-- **`Or_x^{f|W}` has exactly two elements.** -/
theorem exists_two_or (hf : B.IsScFredholmSectionTame f) {x : X} (hx : x ∈ D.carrier)
    (hs : x ∈ PX.smoothSet) :
    ∃ o₁ o₂ : D.Or hf x hx hs, o₁ ≠ o₂ ∧ ∀ o, o = o₁ ∨ o = o₂ :=
  exists_two_orx (D.isFredholm hf).toIsScFredholmSection (mem_smoothSet hx hs) D.hasSections

/-! ### Constructions of domains -/

/-- **The base domain of a chart of the atlas** containing a point. -/
def ofChart {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts) {x : X}
    (hx : x ∈ c.φ.source) : B.Dom where
  carrier := c.φ.source
  isOpen := c.φ.isOpen_source
  nonempty := ⟨x, hx⟩
  exists_chart := ⟨c, hc, subset_rfl⟩

/-- **The intersection of two domains** with a common point. -/
def inter (h : (D.carrier ∩ D'.carrier).Nonempty) : B.Dom where
  carrier := D.carrier ∩ D'.carrier
  isOpen := D.isOpen.inter D'.isOpen
  nonempty := h
  exists_chart := let ⟨c, hc, hsub⟩ := D.exists_chart; ⟨c, hc, fun _ hy => hsub hy.1⟩

/-- **The part of a domain in an open set** meeting it. -/
def restrict {W : Set X} (hW : IsOpen W) (h : (D.carrier ∩ W).Nonempty) : B.Dom where
  carrier := D.carrier ∩ W
  isOpen := D.isOpen.inter hW
  nonempty := h
  exists_chart := let ⟨c, hc, hsub⟩ := D.exists_chart; ⟨c, hc, fun _ hy => hsub hy.1⟩

@[simp] theorem ofChart_carrier {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts) {x : X}
    (hx : x ∈ c.φ.source) : (ofChart hc hx).carrier = c.φ.source := rfl

@[simp] theorem inter_carrier (h : (D.carrier ∩ D'.carrier).Nonempty) :
    (D.inter D' h).carrier = D.carrier ∩ D'.carrier := rfl

@[simp] theorem restrict_carrier {W : Set X} (hW : IsOpen W) (h : (D.carrier ∩ W).Nonempty) :
    (D.restrict hW h).carrier = D.carrier ∩ W := rfl

end StrongBundle.Dom

variable (B) in
/-- **The chosen domain at a point**: the base domain of the chosen chart `orChart B x` of the
atlas through `x`. -/
def StrongBundle.domAt (x : X) : B.Dom :=
  StrongBundle.Dom.ofChart (B.exists_chart_mem x).choose_spec.1 (mem_orChart x)

variable (B) in
theorem StrongBundle.mem_domAt (x : X) : x ∈ (B.domAt x).carrier := mem_orChart x

variable (B) in
theorem StrongBundle.domAt_carrier (x : X) : (B.domAt x).carrier = (orChart B x).φ.source := rfl

namespace StrongBundle.Dom

variable (D D' D'' : B.Dom)

/-! ### The identification of two domains over their intersection -/

/-- **The identification of `P|W` and `P|W'` over `W ∩ W'`**, a local strong bundle isomorphism
with base map `w ↦ w`. -/
def iso : LocalIso D.bundle D'.bundle {w : D.carrier | w.1 ∈ D'.carrier}
    {w' : D'.carrier | w'.1 ∈ D.carrier} :=
  B.restrictIsoInter D.isOpen D'.isOpen

theorem iso_ϕ_of_mem {w : D.carrier} (hw : w.1 ∈ D'.carrier) :
    (D.iso D').ϕ w = ⟨w.1, hw⟩ :=
  B.restrictIsoInter_ϕ_of_mem D.isOpen D'.isOpen hw

theorem iso_ϕ_mk {x : X} (hx : x ∈ D.carrier) (hx' : x ∈ D'.carrier) :
    (D.iso D').ϕ ⟨x, hx⟩ = ⟨x, hx'⟩ :=
  D.iso_ϕ_of_mem D' hx'

/-- **The restrictions of a section to two domains correspond** under `Dom.iso`. -/
theorem sec_eqOn_iso (hfs : IsSection P f) :
    EqOn (D.sec f hfs) ((D.iso D').Ψ ∘ D'.sec f hfs ∘ (D.iso D').ϕ)
      {w : D.carrier | w.1 ∈ D'.carrier} :=
  B.restrictSection_eqOn_restrictIsoInter D.isOpen D'.isOpen hfs

/-- **The composite of the identifications `W → W' → W''` is the identification `W → W''`** over
`W ∩ W' ∩ W''`. -/
theorem iso_comp_germ {x : X} (hx : x ∈ D.carrier) (hx' : x ∈ D'.carrier)
    (hx'' : x ∈ D''.carrier) :
    ∃ W : Set D.carrier, IsOpen W ∧ (⟨x, hx⟩ : D.carrier) ∈ W ∧
      (∀ y ∈ W, (D'.iso D'').ϕ ((D.iso D').ϕ y) = (D.iso D'').ϕ y) ∧
      ∀ w, pullbackProj P (Subtype.val : D.carrier → X) w ∈ W →
        (D'.iso D'').Φ ((D.iso D').Φ w) = (D.iso D'').Φ w := by
  refine ⟨{w : D.carrier | w.1 ∈ D'.carrier ∩ D''.carrier},
    (D'.isOpen.inter D''.isOpen).preimage continuous_subtype_val, ⟨hx', hx''⟩,
    fun y hy => ?_, fun w hw => ?_⟩
  · rw [D.iso_ϕ_of_mem D' hy.1, D.iso_ϕ_of_mem D'' hy.2]
    exact D'.iso_ϕ_of_mem D'' hy.2
  · have h1 : P w.1.2 ∈ D'.carrier := by
      rw [StrongBundle.pullbackSpace_subtypeVal_proj w]; exact hw.1
    change B.restrictIsoInv D''.carrier (B.restrictIsoInv D'.carrier w.1.2).1.2 =
      B.restrictIsoInv D''.carrier w.1.2
    rw [B.restrictIsoInv_snd h1]

/-- **The identification of a domain with itself is the identity.** -/
theorem iso_self_germ {x : X} (hx : x ∈ D.carrier) :
    ∃ W : Set D.carrier, IsOpen W ∧ (⟨x, hx⟩ : D.carrier) ∈ W ∧
      W ⊆ {w : D.carrier | w.1 ∈ D.carrier} ∧ (∀ y ∈ W, (D.iso D).ϕ y = y) ∧
      ∀ w, pullbackProj P (Subtype.val : D.carrier → X) w ∈ W → (D.iso D).Φ w = w :=
  ⟨univ, isOpen_univ, mem_univ _, fun w _ => w.2, fun y _ => D.iso_ϕ_of_mem D y.2,
    fun w _ => B.restrictIsoInv_snd_self w⟩

/-! ### The comparison maps -/

/-- **The comparison map** `Or_x^{f|W'} ≃ Or_x^{f|W}` for a smooth point `x` of two domains
`W`, `W'`: the orientation map of the identification of `P|W` and `P|W'` near `x`. -/
def compare (hf : B.IsScFredholmSectionTame f) (x : X) (hx : x ∈ D.carrier)
    (hx' : x ∈ D'.carrier) (hs : x ∈ PX.smoothSet) : D'.Or hf x hx' hs ≃ D.Or hf x hx hs :=
  (D.iso D').orxViaAt (D.isFredholm hf).toIsScFredholmSection
    (D'.isFredholm hf).toIsScFredholmSection (D.sec_eqOn_iso D' hf.isScSmooth.1) D.hasSections
    D'.hasSections (a := ⟨x, hx⟩) hx' (mem_smoothSet hx hs) (D.iso_ϕ_mk D' hx hx')

/-- **The comparison map of a domain with itself is the identity.** -/
theorem compare_self (hf : B.IsScFredholmSectionTame f) (x : X) (hx : x ∈ D.carrier)
    (hs : x ∈ PX.smoothSet) : D.compare D hf x hx hx hs = Equiv.refl _ :=
  (D.iso D).orxViaAt_of_germ_id (D.isFredholm hf).toIsScFredholmSection
    (D.sec_eqOn_iso D hf.isScSmooth.1) D.hasSections (b := ⟨x, hx⟩) hx (mem_smoothSet hx hs)
    (D.iso_ϕ_mk D hx hx) (D.iso_self_germ hx)

/-- **The cocycle condition for the comparison maps**: for a smooth point `x` of three domains,
`Or_x^{f|W''} → Or_x^{f|W'} → Or_x^{f|W}` is the comparison map `Or_x^{f|W''} → Or_x^{f|W}`. -/
theorem compare_trans (hf : B.IsScFredholmSectionTame f) (x : X) (hx : x ∈ D.carrier)
    (hx' : x ∈ D'.carrier) (hx'' : x ∈ D''.carrier) (hs : x ∈ PX.smoothSet) :
    (D'.compare D'' hf x hx' hx'' hs).trans (D.compare D' hf x hx hx' hs) =
      D.compare D'' hf x hx hx'' hs :=
  StrongBundle.LocalIso.orxViaAt_triangle (L := D'.iso D'') (L₂ := D.iso D') (N := D.iso D'')
    (D.isFredholm hf).toIsScFredholmSection (D'.isFredholm hf).toIsScFredholmSection
    (D''.isFredholm hf).toIsScFredholmSection (D'.sec_eqOn_iso D'' hf.isScSmooth.1)
    (D.sec_eqOn_iso D' hf.isScSmooth.1) (D.sec_eqOn_iso D'' hf.isScSmooth.1) D.hasSections
    D'.hasSections D''.hasSections (b := ⟨x, hx⟩) hx' hx'' (mem_smoothSet hx hs)
    (D.iso_ϕ_mk D' hx hx') (x₁ := ⟨x, hx'⟩) hx'' (D'.iso_ϕ_mk D'' hx' hx'')
    (D.iso_ϕ_mk D'' hx hx'') (D.iso_comp_germ D' D'' hx hx' hx'')

/-- **The comparison maps in the two directions are inverse to each other.** -/
theorem compare_symm (hf : B.IsScFredholmSectionTame f) (x : X) (hx : x ∈ D.carrier)
    (hx' : x ∈ D'.carrier) (hs : x ∈ PX.smoothSet) :
    (D.compare D' hf x hx hx' hs).symm = D'.compare D hf x hx' hx hs := by
  have h := (D.compare_trans D' D hf x hx hx' hx hs).trans (D.compare_self hf x hx hs)
  refine Equiv.ext fun o => ?_
  have h' := congrFun (congrArg DFunLike.coe h) o
  exact ((Equiv.eq_symm_apply (D.compare D' hf x hx hx' hs)).2 h').symm

end StrongBundle.Dom

/-! ### The local orientation sets -/

/-- **The local orientation set `Or_x^f`** of an sc-Fredholm section with tame germ data at a
smooth point `x`: the orientations of `DET(f|W, x)` for the chosen domain `W` at `x`, the base
domain of a chart of the atlas through `x`.  The linearizations are those of `f − s` for the
sc⁺-sections `s` defined over `W`. -/
abbrev OrxLoc (hf : B.IsScFredholmSectionTame f) (x : X) (hs : x ∈ PX.smoothSet) : Type _ :=
  (B.domAt x).Or hf x (B.mem_domAt x) hs

/-- **The local orientation set has exactly two elements.** -/
theorem exists_two_orxLoc (hf : B.IsScFredholmSectionTame f) {x : X} (hs : x ∈ PX.smoothSet) :
    ∃ o₁ o₂ : OrxLoc hf x hs, o₁ ≠ o₂ ∧ ∀ o, o = o₁ ∨ o = o₂ :=
  (B.domAt x).exists_two_or hf (B.mem_domAt x) hs

namespace StrongBundle.Dom

variable (D D' : B.Dom)

/-- **The local orientation set read in a domain**: `Or_x^f ≃ Or_x^{f|W}` for every domain
`W ∋ x`, the comparison map with the chosen domain at `x`. -/
def toLoc (hf : B.IsScFredholmSectionTame f) (x : X) (hx : x ∈ D.carrier)
    (hs : x ∈ PX.smoothSet) : OrxLoc hf x hs ≃ D.Or hf x hx hs :=
  D.compare (B.domAt x) hf x hx (B.mem_domAt x) hs

/-- **The identifications of `Or_x^f` with `Or_x^{f|W}` are compatible with the comparison
maps.** -/
theorem toLoc_compare (hf : B.IsScFredholmSectionTame f) (x : X) (hx : x ∈ D.carrier)
    (hx' : x ∈ D'.carrier) (hs : x ∈ PX.smoothSet) :
    (D'.toLoc hf x hx' hs).trans (D.compare D' hf x hx hx' hs) = D.toLoc hf x hx hs :=
  D.compare_trans D' (B.domAt x) hf x hx hx' (B.mem_domAt x) hs

/-- In the chosen domain at `x` the identification is the identity. -/
theorem toLoc_domAt (hf : B.IsScFredholmSectionTame f) (x : X) (hs : x ∈ PX.smoothSet) :
    (B.domAt x).toLoc hf x (B.mem_domAt x) hs = Equiv.refl _ :=
  (B.domAt x).compare_self hf x (B.mem_domAt x) hs

/-! ### Transport along paths in the smaller of two domains -/

variable {D D'}

/-- The inclusion of a domain into a larger one. -/
def incl (h : D.carrier ⊆ D'.carrier) (w : D.carrier) : D'.carrier := ⟨w.1, h w.2⟩

@[simp] theorem incl_val (h : D.carrier ⊆ D'.carrier) (w : D.carrier) : (incl h w).1 = w.1 :=
  rfl

/-- An sc-smooth path in a domain is an sc-smooth path in every larger domain. -/
theorem isScSmoothMap_incl_comp (h : D.carrier ⊆ D'.carrier) {γ : (Fin 1 → ℝ) → D.carrier}
    (hγ : (rnPolyfold 1).IsScSmoothMap (PX.restrictOpen D.isOpen) γ) :
    (rnPolyfold 1).IsScSmoothMap (PX.restrictOpen D'.isOpen) (fun q => incl h (γ q)) := by
  have e : (fun q => (B.restrictIsoOf D.isOpen D'.isOpen h).ϕ (γ q)) = fun q => incl h (γ q) :=
    funext fun q => B.restrictIsoOf_ϕ D.isOpen D'.isOpen h (γ q)
  exact e ▸ (B.restrictIsoOf D.isOpen D'.isOpen h).isScSmoothMap_comp_or hγ fun _ => mem_univ _

/-- The identification of two domains `W ⊆ W'` over `W` and the inclusion `P|W → P|W'` have the
same germ at every point of `W`. -/
theorem germEq_iso_restrictIsoOf (h : D.carrier ⊆ D'.carrier) (a : D.carrier) :
    StrongBundle.LocalIso.GermEq (D.iso D') (B.restrictIsoOf D.isOpen D'.isOpen h) a :=
  ⟨⟨univ, isOpen_univ, mem_univ a, fun w _ => h w.2, subset_rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩⟩

/-- **The comparison map for `W ⊆ W'` is the orientation map of the inclusion** `P|W → P|W'`. -/
theorem compare_eq_orxViaAt_restrictIsoOf (h : D.carrier ⊆ D'.carrier)
    (hf : B.IsScFredholmSectionTame f) (x : X) (hx : x ∈ D.carrier) (hs : x ∈ PX.smoothSet) :
    D.compare D' hf x hx (h hx) hs =
      (B.restrictIsoOf D.isOpen D'.isOpen h).orxViaAt (D.isFredholm hf).toIsScFredholmSection
        (D'.isFredholm hf).toIsScFredholmSection
        (B.restrictSection_eqOn_restrictIsoOf D.isOpen D'.isOpen h hf.isScSmooth.1)
        D.hasSections D'.hasSections (a := ⟨x, hx⟩) (mem_univ _) (mem_smoothSet hx hs)
        (B.restrictIsoOf_ϕ D.isOpen D'.isOpen h ⟨x, hx⟩) :=
  StrongBundle.LocalIso.orxViaAt_germ _ _ _ _ _ _ _ _ _ _ _ (germEq_iso_restrictIsoOf h ⟨x, hx⟩)

/-- **The comparison maps intertwine the transports of two domains `W ⊆ W'`**: for an sc-smooth
path `γ` in `W` from `x₀` to `x₁`, the comparison map at `x₀` followed by the transport of
`f|W` along `γ` is the transport of `f|W'` along `γ` followed by the comparison map at `x₁`. -/
theorem compare_transport (h : D.carrier ⊆ D'.carrier) (hX : PX.IsTame)
    (hf : B.IsScFredholmSectionTame f) {γ : (Fin 1 → ℝ) → D.carrier}
    (hγ : (rnPolyfold 1).IsScSmoothMap (PX.restrictOpen D.isOpen) γ) {x₀ x₁ : X}
    (hx₀ : x₀ ∈ D.carrier) (hx₁ : x₁ ∈ D.carrier) (h₀ : γ (pt1 0) = ⟨x₀, hx₀⟩)
    (h₁ : γ (pt1 1) = ⟨x₁, hx₁⟩) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    (D.compare D' hf x₀ hx₀ (h hx₀) hs₀).trans
      ((D.transport hX hf).transport γ hγ h₀ h₁ (mem_smoothSet hx₀ hs₀)
        (mem_smoothSet hx₁ hs₁)) =
    ((D'.transport hX hf).transport (fun q => incl h (γ q)) (isScSmoothMap_incl_comp h hγ)
      (congrArg (incl h) h₀) (congrArg (incl h) h₁) (mem_smoothSet (h hx₀) hs₀)
      (mem_smoothSet (h hx₁) hs₁)).trans (D.compare D' hf x₁ hx₁ (h hx₁) hs₁) := by
  set L := B.restrictIsoOf D.isOpen D'.isOpen h with hL
  have hfL := B.restrictSection_eqOn_restrictIsoOf D.isOpen D'.isOpen h hf.isScSmooth.1
  -- the statement for the inclusion, with endpoints `x₀'`, `x₁'` and a path `γ'` in `W'`
  have key : ∀ (γ' : (Fin 1 → ℝ) → D'.carrier) (_ : γ' = fun q => L.ϕ (γ q))
      (hγ' : (rnPolyfold 1).IsScSmoothMap (PX.restrictOpen D'.isOpen) γ')
      (a₀ a₁ : D.carrier) (h₀ : γ (pt1 0) = a₀) (h₁ : γ (pt1 1) = a₁)
      (has₀ : a₀ ∈ (PX.restrictOpen D.isOpen).smoothSet)
      (has₁ : a₁ ∈ (PX.restrictOpen D.isOpen).smoothSet)
      (x₀' x₁' : D'.carrier) (e₀ : L.ϕ a₀ = x₀') (e₁ : L.ϕ a₁ = x₁')
      (h₀' : γ' (pt1 0) = x₀') (h₁' : γ' (pt1 1) = x₁')
      (hs₀' : x₀' ∈ (PX.restrictOpen D'.isOpen).smoothSet)
      (hs₁' : x₁' ∈ (PX.restrictOpen D'.isOpen).smoothSet),
      (L.orxViaAt (D.isFredholm hf).toIsScFredholmSection
        (D'.isFredholm hf).toIsScFredholmSection hfL D.hasSections D'.hasSections
        (mem_univ a₀) has₀ e₀).trans ((D.transport hX hf).transport γ hγ h₀ h₁ has₀ has₁) =
      ((D'.transport hX hf).transport γ' hγ' h₀' h₁' hs₀' hs₁').trans
        (L.orxViaAt (D.isFredholm hf).toIsScFredholmSection
          (D'.isFredholm hf).toIsScFredholmSection hfL D.hasSections D'.hasSections
          (mem_univ a₁) has₁ e₁) := by
    rintro γ' rfl hγ' a₀ a₁ h₀ h₁ has₀ has₁ x₀' x₁' rfl rfl h₀' h₁' hs₀' hs₁'
    exact L.orxVia_comm_of_chart (D.isTame hX) D.exists_chart_univ (D.isFredholm hf)
      D.hasSections (D'.isTame hX) D'.exists_chart_univ (D'.isFredholm hf) D'.hasSections hfL
      hγ h₀ h₁ has₀ has₁
  rw [compare_eq_orxViaAt_restrictIsoOf h hf x₀ hx₀ hs₀,
    compare_eq_orxViaAt_restrictIsoOf h hf x₁ hx₁ hs₁]
  exact key _ (funext fun q => (B.restrictIsoOf_ϕ D.isOpen D'.isOpen h (γ q)).symm) _ _ _ h₀ h₁
    _ _ _ _ _ _ _ _ _ _

/-! ### Comparison with the linearizations made with sc⁺-sections over all of the base -/

variable (D) in
/-- **With sc⁺-sections of `P` through all smooth fibre points, `Lin(f|W, x)` is `Lin(f, x)`**:
for a chart point `p` of `P` at a smooth `x ∈ W` whose base domain lies in the domain `W`, the
linearizations of `f|W` read in the chart point carried to `P|W` are those of `f` read in
`p`. -/
theorem linSet_restrictIso (hf : B.IsScFredholmSection f) (hsec : B.HasScPlusSectionsThrough)
    {x : X} (hx : x ∈ D.carrier) (hs : x ∈ PX.smoothSet) (p : ChartPoint B x)
    (hp : p.c.φ.source ⊆ D.carrier) :
    ((B.restrictIso D.isOpen).mpullPt p hp (a := ⟨x, hx⟩) (mem_univ _) rfl).linSet
      (D.sec f hf.isScSmooth.1) = p.linSet f :=
  StrongBundle.LocalIso.linSet_mpullPt (hf.restrictOpen D.isOpen) hf
    (B.restrictSection_eqOn_restrictIso D.isOpen hf.isScSmooth.1)
    D.hasSections hsec (mem_smoothSet hx hs) hs

end StrongBundle.Dom

end Polyfold
