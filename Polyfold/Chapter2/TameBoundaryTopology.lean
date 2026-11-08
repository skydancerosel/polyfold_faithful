import Polyfold.Chapter2.TameBoundary

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, Appendix §2.7.4,
**Proposition 2.7.12** (p. 83), **Theorem 2.7.13** (pp. 83–84), **Definition 2.7.14** (p. 84),
**Lemma 2.7.15** (p. 85) and **Proposition 2.7.16** (pp. 85–87), all new in the 2021 edition.
The sets `bX`, `U(x, V, θ)` and the maps `Φ_{(x,V,θ)}`, `B` are those of
`Polyfold/Chapter2/TameBoundary.lean`.

# The natural topology of the tame boundary `bX`

## The text, paraphrased

(§2.7.4.3) A set `U ⊆ bX` belongs to `T_{bX}` if every class in `U` has a representative
`(x, V, θ)` and a set `O ⊆ U ∩ U(x, V, θ)` with `Φ_{(x,V,θ)}(O)` open in `θ`; alternatively, if
every class in `U` has a representative with `U(x, V, θ) ⊆ U` ("take `V` small").
(Lemma 2.7.15) `T_{bX}` is a topology; the proof of the intersection axiom uses that the
transition maps are homeomorphisms.  (Before Proposition 2.7.12) If `U(x, V, θ)` and
`U(x', V', θ')` meet at `[y, U, σ]`, then near `y` the face `σ` is an open subset of `θ` and of
`θ'`, and the transition map `Φ_{(x',V',θ')} ∘ Φ_{(x,V,θ)}⁻¹` is the identity of `σ` near `y`.
(Proposition 2.7.12) The images of `U(x, V, θ) ∩ U(x', V', θ')` are open in `θ` and `θ'`, and the
transition map is an sc-diffeomorphism.  (Theorem 2.7.13) For a tame `X`: (1) `bX` has a
natural metrizable topology; (2) it has a natural tame M-polyfold structure; (3) `B` is
sc-smooth; (4) `d_X(B(p)) − 1 = d_{bX}(p)`; the topology and the structure are characterized by:
every `U(x, V, θ)` is open and every `Φ_{(x,V,θ)}` is a homeomorphism and an sc-diffeomorphism
onto `θ`.  (Definition 2.7.14) The tame boundary of `X` is `B : bX → X`, with image `∂X`; it can
be iterated, `bᵏX` and `Bᵏ : bᵏX → X` ((2.45)–(2.47)).  (Proposition 2.7.16) `T_{bX}` is
metrizable: it is Hausdorff (two cases, `x ≠ x'` and `x = x'`), locally metrizable through the
`Φ`, and paracompact (a locally finite refinement built from a locally finite refinement of the
cover `(V_x)` of `∂X`), so Nagata–Smirnov applies.

## What is formalized

All results are proved for an abstract `d : X → ℕ` with the corner axioms
(`TameBoundary.IsCornerIndex`) and then specialized to tame M-polyfolds (`namespace MPolyfold`).
* `IsBOpen` (the first characterization), `isBOpen_iff` (the alternative one), the topology
  `bTopology` (**Lemma 2.7.15**, `lemma_2_7_15`, `MPolyfold.lemma_2_7_15_2021`), `isOpen_uSet`,
  `isTopologicalBasis_uSet`, `continuous_bMap`.
* **Proposition 2.7.12**, topological part: `proposition_2_7_12`,
  `MPolyfold.proposition_2_7_12_2021` (the two images are open, the transition map is the
  identity on underlying points of `X`); `isOpenEmbedding_phi` (every `Φ_{(x,V,θ)}` is an open
  embedding into `θ`) and `phiHomeomorph` (a homeomorphism onto `θ` for `V` centred at `x`).
* **Proposition 2.7.16**: `T2Space (BSpace hd)` and `proposition_2_7_16`
  (`MPolyfold.proposition_2_7_16_2021`).
* **Theorem 2.7.13**, topological part: `theorem_2_7_13_topology`,
  `MPolyfold.theorem_2_7_13_2021`: (1) metrizability; the characterization of the topology
  (`eq_of_isOpen_uSet`: a topology in which every `U(x, V, θ)` is open and every `Φ` is open
  onto its image is `T_{bX}`); continuity of `B`, its image `∂X`, and the fibre count
  `#B⁻¹(x) = d_X(x)` (the set-level content of (4)).
* **Definition 2.7.14**, topological part: `MPolyfold.tameBoundary`, the continuous map
  `B : bX → X`.

## What the text leaves implicit, and the choices made

* The first characterization of `T_{bX}` is read with `O` containing the class in question
  (otherwise `O = ∅` would make every set open).
* Lemma 2.7.15 is proved directly from the alternative characterization and a common refinement
  of equivalent triples (`BRel.exists_common`), without the sc-smoothness of transition maps.
* Proposition 2.7.16 is proved with the pullback form of Smirnov's theorem used for M-polyfolds
  (`metrizableSpace_of_pullback`, `Metrizable.lean`): `bX` is Hausdorff and each point has an
  open neighbourhood `B⁻¹(W) ∩ ⋃ U(x, W, θ)` embedded into the metrizable `X × ℝ^{faces}` by `B`
  and the indicators of the clopen sets `U(x, W, θ)`; this replaces the text's paracompactness
  argument.
* `Φ_{(x,V,θ)}` is onto `θ` only for `V` centred at `x` (see the header of `TameBoundary.lean`);
  `isOpenEmbedding_phi` holds for all `V`.
* Not formalized: Theorem 2.7.13 (2) (the tame M-polyfold structure on `bX`), (3) (sc-smoothness
  of `B`), (4) beyond the fibre count (`d_{bX}` needs (2)), the sc-diffeomorphism part of
  Proposition 2.7.12 and of the characterization, and the iterated boundaries `bᵏX`, `Bᵏ`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace TameBoundary

universe u

variable {X : Type u} [TopologicalSpace X]

/-! ### The natural topology `T_{bX}` (Lemma 2.7.15) -/

section Topology

variable {d : X → ℕ} (hd : IsCornerIndex d)

/-- **The natural topology of 2021 §2.7.4.3**: `U ∈ T_{bX}` iff every `[x, V, θ] ∈ U` has a
representative `(x, V, θ)` and a set `O ∋ [x, V, θ]`, `O ⊆ U ∩ U(x, V, θ)`, with `Φ_{(x,V,θ)}(O)`
open in `θ`. -/
def IsBOpen (U : Set (BSpace hd)) : Prop :=
  ∀ p ∈ U, ∃ t : BTriple hd, t.cls = p ∧ ∃ O ⊆ U ∩ uSet hd t, p ∈ O ∧
    ∃ N, IsOpen N ∧ bMap hd '' O = N ∩ t.θ

include hd

/-- Shrinking the neighbourhood: for an open `N ∋ x` there is an equivalent triple
`(x, V ∩ N, θ')` with `U(x, V ∩ N, θ') ⊆ U(x, V, θ)`. -/
theorem BTriple.exists_shrink (t : BTriple hd) {N : Set X} (hN : IsOpen N) (hx : t.x ∈ N) :
    ∃ t' : BTriple hd, t'.cls = t.cls ∧ t'.x = t.x ∧ t'.V ⊆ N ∧ uSet hd t' ⊆ uSet hd t := by
  have hV' := mem_faceStructuredNbhdsAt_of_subset hd t.mem (t.mem.1.1.1.inter hN)
    ⟨t.mem.2.1, hx⟩ inter_subset_left
  obtain ⟨θ', hθ', he⟩ :=
    exists_faceExt_eq hd hV'.1.1.1 t.mem.1.1.1 inter_subset_left hV'.2.1 t.mem_faces
  let t' : BTriple hd := ⟨⟨t.x, t.V ∩ N, hV', t.one_le⟩, θ', hθ'⟩
  refine ⟨t', ?_, rfl, inter_subset_right,
    uSet_subset hd (s := t') (t := t) (isMor_of_subset inter_subset_left t.mem) he⟩
  rw [BTriple.cls_eq_cls]
  exact ⟨rfl, t.V ∩ N, hV', fun z hz => ⟨hz, hz.1⟩, θ', hθ', faceExt_self hd hV'.1.1.1 hθ'.1, he⟩

/-- Two equivalent triples have a common refinement. -/
theorem BRel.exists_common {s t : BTriple hd} (h : BRel hd s t) :
    ∃ r : BTriple hd, r.cls = s.cls ∧ r.x = s.x ∧ r.V ⊆ s.V ∧ faceExt d s.V r.θ = s.θ ∧
      uSet hd r ⊆ uSet hd s ∩ uSet hd t := by
  obtain ⟨hx, V'', hV'', hsub, θ'', hθ'', e₁, e₂⟩ := h
  let r : BTriple hd := ⟨⟨s.x, V'', hV'', s.one_le⟩, θ'', hθ''⟩
  have hrs : IsMor d r.x r.V s.x s.V := isMor_of_subset (fun z hz => (hsub hz).1) s.mem
  have hrt : IsMor d r.x r.V t.x t.V := by
    have := isMor_of_subset (x := s.x) (fun z hz => (hsub hz).2) (hx ▸ t.mem)
    rw [hx] at this ⊢; exact this
  refine ⟨r, ?_, rfl, fun z hz => (hsub hz).1, e₁, fun z hz =>
    ⟨uSet_subset hd hrs e₁ hz, uSet_subset hd hrt e₂ hz⟩⟩
  rw [BTriple.cls_eq_cls]
  exact ⟨rfl, V'', hV'', fun z hz => ⟨hz, (hsub hz).1⟩, θ'', hθ'',
    faceExt_self hd hV''.1.1.1 hθ''.1, e₁⟩

/-- `U(x, V, θ) ∩ U(x', V, θ') ≠ ∅` forces `θ = θ'` (same `V`). -/
theorem eq_of_mem_uSet {t₁ t₂ : BTriple hd} (hV : t₁.V = t₂.V) {p : BSpace hd}
    (h₁ : p ∈ uSet hd t₁) (h₂ : p ∈ uSet hd t₂) : t₁.θ = t₂.θ := by
  obtain ⟨a, rfl, -, ha, hae⟩ := h₁
  obtain ⟨b, hab, -, hb, hbe⟩ := h₂
  rw [BTriple.cls_eq_cls] at hab
  obtain ⟨-, V'', -, hsub, θ'', hθ'', e₁, e₂⟩ := hab
  have hbV : b.V ⊆ t₁.V := by rw [hV]; exact hb.1
  rw [← hae, ← hbe, ← e₁, ← e₂, ← hV,
    faceExt_faceExt hd b.mem.1.1.1 t₁.mem.1.1.1 (fun z hz => (hsub hz).1) hbV hθ''.1,
    faceExt_faceExt hd a.mem.1.1.1 t₁.mem.1.1.1 (fun z hz => (hsub hz).2) ha.1 hθ''.1]

/-- **The alternative characterization** (2021 §2.7.4.3): `U ∈ T_{bX}` iff every point of `U` has a
representative `(x, V, θ)` with `U(x, V, θ) ⊆ U`. -/
theorem isBOpen_iff {U : Set (BSpace hd)} :
    IsBOpen hd U ↔ ∀ p ∈ U, ∃ t : BTriple hd, t.cls = p ∧ uSet hd t ⊆ U := by
  constructor
  · intro h p hp
    obtain ⟨t, rfl, O, hOU, hpO, N, hN, hON⟩ := h p hp
    have hxN : t.x ∈ N := by
      have : t.x ∈ bMap hd '' O := ⟨_, hpO, rfl⟩
      rw [hON] at this; exact this.1
    obtain ⟨t', ht', hx', hV'N, hsub⟩ := t.exists_shrink hd hN hxN
    refine ⟨t', ht', fun q hq => ?_⟩
    have hqt := hsub hq
    have hBq : bMap hd q ∈ N ∩ t.θ :=
      ⟨hV'N (t'.mem_faces.1.subset (bMap_mem_of_mem_uSet hd hq)), bMap_mem_of_mem_uSet hd hqt⟩
    rw [← hON] at hBq
    obtain ⟨o, hoO, hoq⟩ := hBq
    have : o = q := bMap_injOn_uSet hd t (hOU hoO).2 hqt hoq
    exact (hOU (this ▸ hoO)).1
  · intro h p hp
    obtain ⟨t, rfl, hsub⟩ := h p hp
    exact ⟨t, rfl, uSet hd t, fun q hq => ⟨hsub hq, hq⟩, cls_mem_uSet hd t, reach d t.V t.x,
      isOpen_reach hd t.mem.1.1.1 t.x, by rw [bMap_image_uSet hd, inter_comm]⟩

/-- **2021 Lemma 2.7.15**: `T_{bX}` is a topology on `bX`. -/
instance bTopology : TopologicalSpace (BSpace hd) where
  IsOpen := IsBOpen hd
  isOpen_univ := (isBOpen_iff hd).2 fun p _ => by
    obtain ⟨t, ht⟩ := BSpace.exists_rep hd p
    exact ⟨t, ht, subset_univ _⟩
  isOpen_inter U₁ U₂ h₁ h₂ := by
    rw [isBOpen_iff hd] at h₁ h₂ ⊢
    rintro p ⟨hp₁, hp₂⟩
    obtain ⟨t₁, rfl, hs₁⟩ := h₁ _ hp₁
    obtain ⟨t₂, ht₂, hs₂⟩ := h₂ _ hp₂
    obtain ⟨r, hr, -, -, -, hsub⟩ := BRel.exists_common hd ((BTriple.cls_eq_cls hd).1 ht₂.symm)
    exact ⟨r, hr, fun q hq => ⟨hs₁ (hsub hq).1, hs₂ (hsub hq).2⟩⟩
  isOpen_sUnion S hS := by
    simp only [isBOpen_iff hd] at hS ⊢
    rintro p ⟨U, hU, hpU⟩
    obtain ⟨t, ht, hsub⟩ := hS U hU p hpU
    exact ⟨t, ht, hsub.trans (subset_sUnion_of_mem hU)⟩

theorem isOpen_iff_isBOpen {U : Set (BSpace hd)} : IsOpen U ↔ IsBOpen hd U := Iff.rfl

theorem isOpen_iff_forall_uSet {U : Set (BSpace hd)} :
    IsOpen U ↔ ∀ p ∈ U, ∃ t : BTriple hd, t.cls = p ∧ uSet hd t ⊆ U := isBOpen_iff hd

/-- **2021 Lemma 2.7.15**, as a statement: there is a (unique) topology on `bX` whose open sets
are the sets of `T_{bX}`. -/
theorem lemma_2_7_15 : ∃ τ : TopologicalSpace (BSpace hd), ∀ U, IsOpen[τ] U ↔ IsBOpen hd U :=
  ⟨inferInstance, fun _ => Iff.rfl⟩

/-- The sets `U(x, V, θ)` are open. -/
theorem isOpen_uSet (t : BTriple hd) : IsOpen (uSet hd t) := by
  rw [isOpen_iff_forall_uSet hd]
  rintro p ⟨s, rfl, -, hs, hse⟩
  exact ⟨s, rfl, uSet_subset hd hs hse⟩

/-- The sets `U(x, V, θ)` form a basis of `T_{bX}`. -/
theorem isTopologicalBasis_uSet :
    TopologicalSpace.IsTopologicalBasis (range (uSet hd)) := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ fun p U hpU hU => ?_
  · rintro _ ⟨t, rfl⟩; exact isOpen_uSet hd t
  · obtain ⟨t, rfl, hsub⟩ := (isOpen_iff_forall_uSet hd).1 hU p hpU
    exact ⟨uSet hd t, ⟨t, rfl⟩, cls_mem_uSet hd t, hsub⟩

/-- `B : bX → X` is continuous. -/
theorem continuous_bMap : Continuous (bMap hd) := by
  refine ⟨fun N hN => (isOpen_iff_forall_uSet hd).2 fun p hp => ?_⟩
  obtain ⟨t, rfl⟩ := BSpace.exists_rep hd p
  obtain ⟨t', ht', -, hV'N, -⟩ := t.exists_shrink hd hN hp
  exact ⟨t', ht', fun q hq => hV'N (t'.mem_faces.1.subset (bMap_mem_of_mem_uSet hd hq))⟩

/-- **The germ of a face**: if `θ` is a face of `U ⊆ V` through `y` and `V` is face-structured at
`y`, then near `y` the face `faceExt V θ` of `V` agrees with `θ`. -/
theorem exists_nbhd_faceExt_inter_subset {U V θ : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ⊆ V) {y : X} (hy : y ∈ U) (hθ : θ ∈ facesThrough d U y)
    (hVy : (facesThrough d V y).encard = d y) :
    ∃ B, IsOpen B ∧ y ∈ B ∧ faceExt d V θ ∩ B ⊆ θ := by
  obtain ⟨L⟩ := hd.exists_localPieces (hU.mem_nhds hy)
  refine ⟨L.B, L.isOpen_B, L.mem_B, ?_⟩
  obtain ⟨⟨p, hpU, hp1, rfl⟩, hyθ⟩ := hθ
  rw [faceExt_faceAt hd hV hUV hpU hp1]
  have key : L.B ∩ connectedComponentIn (V ∩ {w | d w = 1}) p ⊆
      closure (connectedComponentIn (U ∩ {w | d w = 1}) p) := by
    rintro g ⟨hgB, hgG⟩
    have hg1 : d g = 1 := (connectedComponentIn_subset _ _ hgG).2
    obtain ⟨i, hgi⟩ := mem_iUnion.1 (L.cover ⟨hgB, hg1⟩)
    have hiG := (L.mono hUV).piece_subset_cc ⟨g, hgi, hgG⟩
    have hpt := L.piece_subset i (L.pt_mem i)
    have heq : faceAt d U (L.pt i) = faceAt d U p := by
      refine faceExt_injOn hd hU hV hUV hy hVy ⟨L.isFaceIn_faceAt_pt i, L.mem_faceAt_pt hy i⟩
        ⟨isFaceIn_faceAt hpU hp1, hyθ⟩ ?_
      rw [faceExt_faceAt hd hV hUV hpt.1 hpt.2, faceExt_faceAt hd hV hUV hpU hp1]
      exact ((faceAt_eq_faceAt_iff hd hV (hUV hpt.1) hpt.2).2 (hiG (L.pt_mem i))).symm
    have hgF : g ∈ faceAt d U (L.pt i) := connectedComponentIn_subset_faceAt _
      ((L.isPreconnected i).subset_connectedComponentIn (L.pt_mem i) (L.piece_subset i) hgi)
    rw [heq] at hgF
    exact hgF.2
  rintro z ⟨⟨-, hzcl⟩, hzB⟩
  refine ⟨L.B_subset hzB, ?_⟩
  have := L.isOpen_B.inter_closure ⟨hzB, hzcl⟩
  exact closure_minimal key isClosed_closure this

/-- `Φ_{(x,V,θ)}` is an open map: `B(U ∩ U(x, V, θ))` is open in `θ` for `U` open. -/
theorem exists_isOpen_bMap_image (t : BTriple hd) {U : Set (BSpace hd)} (hU : IsOpen U) :
    ∃ N, IsOpen N ∧ bMap hd '' (U ∩ uSet hd t) = N ∩ t.θ := by
  have hpt : ∀ q ∈ U ∩ uSet hd t, ∃ N, IsOpen N ∧ bMap hd q ∈ N ∧
      N ∩ t.θ ⊆ bMap hd '' (U ∩ uSet hd t) := by
    rintro q ⟨hqU, hqt⟩
    obtain ⟨s₀, rfl, -, hs₀, hs₀e⟩ := hqt
    obtain ⟨s₁, hs₁, hs₁U⟩ := (isOpen_iff_forall_uSet hd).1 hU _ hqU
    obtain ⟨r, hr, hrx, hrV, hre, hrsub⟩ :=
      BRel.exists_common hd ((BTriple.cls_eq_cls hd).1 hs₁.symm)
    have hrs₀ : IsMor d r.x r.V s₀.x s₀.V := by rw [hrx]; exact isMor_of_subset hrV s₀.mem
    have hr₀ : IsMor d r.x r.V t.x t.V := IsMor.trans hd r.mem.2.1 s₀.mem.1.1.1 t.mem.1.1 hrs₀ hs₀
    have hret : faceExt d t.V r.θ = t.θ := by
      rw [← hs₀e, ← hre, faceExt_faceExt hd s₀.mem.1.1.1 t.mem.1.1.1 hrV hs₀.1 r.mem_faces.1]
    have hrU : uSet hd r ⊆ U ∩ uSet hd t :=
      fun z hz => ⟨hs₁U (hrsub hz).2, uSet_subset hd hs₀ hs₀e (hrsub hz).1⟩
    obtain ⟨B, hB, hyB, hBsub⟩ := exists_nbhd_faceExt_inter_subset hd r.mem.1.1.1 t.mem.1.1.1
      hr₀.1 r.mem.2.1 r.mem_faces (t.mem.1.1.2 _ (hr₀.1 r.mem.2.1))
    rw [hret] at hBsub
    refine ⟨B ∩ reach d r.V r.x, hB.inter (isOpen_reach hd r.mem.1.1.1 r.x), ?_, ?_⟩
    · rw [bMap_cls, ← hrx]; exact ⟨hyB, mem_reach_self r.mem.2.1⟩
    · rintro z ⟨⟨hzB, hzR⟩, hzθ⟩
      have hz : z ∈ bMap hd '' uSet hd r := by
        rw [bMap_image_uSet hd]; exact ⟨hBsub ⟨hzθ, hzB⟩, hzR⟩
      exact image_mono hrU hz
  choose N hN hqN hNsub using hpt
  refine ⟨⋃ q, ⋃ hq : q ∈ U ∩ uSet hd t, N q hq,
    isOpen_iUnion fun q => isOpen_iUnion fun hq => hN q hq, ?_⟩
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨mem_iUnion₂.2 ⟨q, hq, hqN q hq⟩, bMap_mem_of_mem_uSet hd hq.2⟩
  · rintro ⟨hz, hzθ⟩
    obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hz
    exact hNsub q hq ⟨hzq, hzθ⟩

/-- `Φ_{(x,V,θ)} : U(x, V, θ) → θ` is an open embedding (a homeomorphism onto the open subset
`θ ∩ V^x` of `θ`). -/
theorem isOpenEmbedding_phi (t : BTriple hd) : Topology.IsOpenEmbedding (phi hd t) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ (phi_injective hd t) ?_
  · exact ((continuous_bMap hd).comp continuous_subtype_val).subtype_mk _
  · intro O hO
    obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 hO
    obtain ⟨N, hN, hNe⟩ := exists_isOpen_bMap_image hd t hU
    refine isOpen_induced_iff.2 ⟨N, hN, ?_⟩
    ext z
    simp only [mem_preimage, mem_image, Subtype.exists]
    constructor
    · intro hz
      have : (z : X) ∈ N ∩ t.θ := ⟨hz, z.2⟩
      rw [← hNe] at this
      obtain ⟨p, ⟨hpU, hpt⟩, hpz⟩ := this
      exact ⟨p, hpt, hpU, Subtype.ext hpz⟩
    · rintro ⟨p, hpt, hpU, rfl⟩
      have : bMap hd p ∈ bMap hd '' (U ∩ uSet hd t) := ⟨p, ⟨hpU, hpt⟩, rfl⟩
      rw [hNe] at this
      exact this.1

/-- For `V` centred at `x`, `Φ_{(x,V,θ)} : U(x, V, θ) → θ` is a homeomorphism (2021 Theorem
2.7.13, last paragraph). -/
def phiHomeomorph {t : BTriple hd} (h : IsCenteredAt d t.x t.V) : uSet hd t ≃ₜ t.θ :=
  (Equiv.ofBijective _ (phi_bijective_of_isCenteredAt hd h)).toHomeomorphOfIsInducing
    (isOpenEmbedding_phi hd t).isInducing

/-- **The uniqueness in 2021 Theorem 2.7.13**: `T_{bX}` is the only topology on `bX` for which
every `U(x, V, θ)` is open and every `Φ_{(x,V,θ)}` is open (maps open sets to sets open in `θ`). -/
theorem eq_of_isOpen_uSet (τ : TopologicalSpace (BSpace hd))
    (h₁ : ∀ t, IsOpen[τ] (uSet hd t))
    (h₂ : ∀ t U, IsOpen[τ] U → ∃ N, IsOpen N ∧ bMap hd '' (U ∩ uSet hd t) = N ∩ t.θ) :
    τ = bTopology hd := by
  ext U
  constructor
  · intro hU
    change IsBOpen hd U
    intro p hp
    obtain ⟨t, rfl⟩ := BSpace.exists_rep hd p
    obtain ⟨N, hN, hNe⟩ := h₂ t U hU
    exact ⟨t, rfl, U ∩ uSet hd t, subset_rfl, ⟨hp, cls_mem_uSet hd t⟩, N, hN, hNe⟩
  · intro hU
    refine (@isOpen_iff_forall_mem_open _ τ U).2 fun q hq => ?_
    obtain ⟨t, ht, hsub⟩ := (isOpen_iff_forall_uSet hd).1 hU q hq
    exact ⟨uSet hd t, hsub, h₁ t, ht ▸ cls_mem_uSet hd t⟩

/-- **2021 Proposition 2.7.12** (the topological part): for two classes with representatives
`(x, V, θ)`, `(x', V', θ')`, the set `Φ(U(x, V, θ) ∩ U(x', V', θ'))` is open in `θ` and in `θ'`,
and the transition map `Φ_{(x',V',θ')} ∘ Φ_{(x,V,θ)}⁻¹` is the identity of the underlying points
of `X` (hence a homeomorphism between these open sets, `isOpenEmbedding_phi`). -/
theorem proposition_2_7_12 (t t' : BTriple hd) :
    (∃ N, IsOpen N ∧ bMap hd '' (uSet hd t ∩ uSet hd t') = N ∩ t.θ) ∧
      (∃ N', IsOpen N' ∧ bMap hd '' (uSet hd t ∩ uSet hd t') = N' ∩ t'.θ) ∧
      ∀ p (h : p ∈ uSet hd t ∩ uSet hd t'),
        (phi hd t' ⟨p, h.2⟩ : X) = (phi hd t ⟨p, h.1⟩ : X) := by
  refine ⟨?_, ?_, fun _ _ => rfl⟩
  · obtain ⟨N, hN, hNe⟩ := exists_isOpen_bMap_image hd t (isOpen_uSet hd t')
    exact ⟨N, hN, by rw [← hNe, inter_comm]⟩
  · exact exists_isOpen_bMap_image hd t' (isOpen_uSet hd t)

/-- **2021 Proposition 2.7.16**, Hausdorff part: `T_{bX}` is Hausdorff (for `X` Hausdorff). -/
instance [T2Space X] : T2Space (BSpace hd) := by
  refine ⟨fun p q hpq => ?_⟩
  obtain ⟨s, rfl⟩ := BSpace.exists_rep hd p
  obtain ⟨t, rfl⟩ := BSpace.exists_rep hd q
  by_cases hx : s.x = t.x
  · -- the same point: refine both to `V* = V_s ∩ V_t`
    have htV : t.V ∈ faceStructuredNbhdsAt d s.x := by rw [hx]; exact t.mem
    have htθ : t.θ ∈ facesThrough d t.V s.x := by rw [hx]; exact t.mem_faces
    have hV := inter_mem_faceStructuredNbhdsAt hd s.mem htV
    obtain ⟨θs, hθs, hes⟩ :=
      exists_faceExt_eq hd hV.1.1.1 s.mem.1.1.1 inter_subset_left hV.2.1 s.mem_faces
    obtain ⟨θt, hθt, het⟩ :=
      exists_faceExt_eq hd hV.1.1.1 t.mem.1.1.1 inter_subset_right hV.2.1 htθ
    let s' : BTriple hd := ⟨⟨s.x, s.V ∩ t.V, hV, s.one_le⟩, θs, hθs⟩
    let t' : BTriple hd := ⟨⟨s.x, s.V ∩ t.V, hV, s.one_le⟩, θt, hθt⟩
    have hs' : s'.cls = s.cls := (BTriple.cls_eq_cls hd).2
      ⟨rfl, s.V ∩ t.V, hV, fun z hz => ⟨hz, hz.1⟩, θs, hθs, faceExt_self hd hV.1.1.1 hθs.1, hes⟩
    have ht' : t'.cls = t.cls := (BTriple.cls_eq_cls hd).2
      ⟨hx, s.V ∩ t.V, hV, fun z hz => ⟨hz, hz.2⟩, θt, hθt, faceExt_self hd hV.1.1.1 hθt.1, het⟩
    refine ⟨uSet hd s', uSet hd t', isOpen_uSet hd s', isOpen_uSet hd t',
      hs' ▸ cls_mem_uSet hd s', ht' ▸ cls_mem_uSet hd t',
      Set.disjoint_left.2 fun r hr₁ hr₂ => hpq ?_⟩
    have hθ : θs = θt := eq_of_mem_uSet hd (t₁ := s') (t₂ := t') rfl hr₁ hr₂
    rw [← hs', ← ht']
    have : s' = t' := by
      simp only [s', t', hθ]
    rw [this]
  · obtain ⟨N₁, N₂, hN₁, hN₂, hx₁, hx₂, hdisj⟩ := t2_separation hx
    obtain ⟨s', hs', -, hs'N, -⟩ := s.exists_shrink hd hN₁ hx₁
    obtain ⟨t', ht', -, ht'N, -⟩ := t.exists_shrink hd hN₂ hx₂
    refine ⟨uSet hd s', uSet hd t', isOpen_uSet hd s', isOpen_uSet hd t',
      hs' ▸ cls_mem_uSet hd s', ht' ▸ cls_mem_uSet hd t',
      Set.disjoint_left.2 fun r hr₁ hr₂ => ?_⟩
    exact Set.disjoint_left.1 hdisj
      (hs'N (s'.mem_faces.1.subset (bMap_mem_of_mem_uSet hd hr₁)))
      (ht'N (t'.mem_faces.1.subset (bMap_mem_of_mem_uSet hd hr₂)))

end Topology

/-! ### Metrizability (Proposition 2.7.16) and Theorem 2.7.13 (1) -/

section Metrizable

open TopologicalSpace

variable {d : X → ℕ} (hd : IsCornerIndex d)
include hd

/-- The triple `(x, W, θ)` for a face `θ` of `W ∈ N_{X,x}` through `x`. -/
def tripleOf {x : X} {W : Set X} (hW : W ∈ faceStructuredNbhdsAt d x)
    (θ : facesThrough d W x) : BTriple hd :=
  ⟨⟨x, W, hW, one_le_of_mem_isFaceIn hd hW.1.1.1 θ.2.1 θ.2.2⟩, θ.1, θ.2⟩

/-- Over a neighbourhood `W ∈ N_{X,x}` centred at `x`, `B⁻¹(W)` is covered by the sets
`U(x, W, θ)`, `θ ∈ F_X(x, W)`. -/
theorem exists_mem_uSet_tripleOf {x : X} {W : Set X} (hW : W ∈ faceStructuredNbhdsAt d x)
    (hc : IsCenteredAt d x W) {p : BSpace hd} (hp : bMap hd p ∈ W) :
    ∃ θ : facesThrough d W x, p ∈ uSet hd (tripleOf hd hW θ) := by
  obtain ⟨s, rfl⟩ := BSpace.exists_rep hd p
  simp only [bMap_cls] at hp
  have hW' := mem_faceStructuredNbhdsAt_of_subset hd s.mem (s.mem.1.1.1.inter hW.1.1.1)
    ⟨s.mem.2.1, hp⟩ inter_subset_left
  obtain ⟨σ, hσ, hσe⟩ :=
    exists_faceExt_eq hd hW'.1.1.1 s.mem.1.1.1 inter_subset_left hW'.2.1 s.mem_faces
  have hθ := faceExt_mem_facesThrough hd hW.1.1.1 inter_subset_right hσ
  refine ⟨⟨_, hθ.1, hc _ hθ.1⟩, ?_⟩
  let r : BTriple hd := ⟨⟨s.x, s.V ∩ W, hW', s.one_le⟩, σ, hσ⟩
  refine ⟨r, ?_, hθ.2, ⟨inter_subset_right, hW.1.1.2 _ hp, fun γ hγ => hc γ hγ.1⟩, rfl⟩
  rw [BTriple.cls_eq_cls]
  exact ⟨rfl, s.V ∩ W, hW', fun z hz => ⟨hz, hz.1⟩, σ, hσ, faceExt_self hd hW'.1.1.1 hσ.1, hσe⟩

/-- The pieces of `B⁻¹(W)`, `W` centred at `x`, are metrizable, open, pairwise disjoint and cover
it; hence `B⁻¹(W)` is metrizable. -/
theorem metrizableSpace_preimage [MetrizableSpace X] {x : X} {W : Set X}
    (hW : W ∈ faceStructuredNbhdsAt d x) (hc : IsCenteredAt d x W) :
    MetrizableSpace (bMap hd ⁻¹' W) := by
  classical
  set Y := bMap hd ⁻¹' W
  let P : facesThrough d W x → Set Y := fun θ => {y | y.1 ∈ uSet hd (tripleOf hd hW θ)}
  have hPo : ∀ θ, IsOpen (P θ) := fun θ =>
    (isOpen_uSet hd _).preimage continuous_subtype_val
  have hcov : ∀ y : Y, ∃ θ, y ∈ P θ := fun y => exists_mem_uSet_tripleOf hd hW hc y.2
  have hdisj : ∀ θ θ' : facesThrough d W x, ∀ y : Y, y ∈ P θ → y ∈ P θ' → θ = θ' :=
    fun θ θ' y h h' => Subtype.ext (eq_of_mem_uSet hd (t₁ := tripleOf hd hW θ)
      (t₂ := tripleOf hd hW θ') rfl h h')
  have hPc : ∀ θ, IsClosed (P θ) := by
    intro θ
    have : (P θ)ᶜ = ⋃ θ' : {θ' // θ' ≠ θ}, P θ'.1 := by
      ext y
      simp only [mem_compl_iff, mem_iUnion]
      constructor
      · intro hy
        obtain ⟨θ', hθ'⟩ := hcov y
        exact ⟨⟨θ', fun h => hy (h ▸ hθ')⟩, hθ'⟩
      · rintro ⟨⟨θ', hne⟩, hy'⟩ hy
        exact hne (hdisj _ _ y hy' hy)
    exact isOpen_compl_iff.1 (this ▸ isOpen_iUnion fun θ' => hPo θ'.1)
  have hfin : Finite (facesThrough d W x) := by
    have : (facesThrough d W x).encard ≠ ⊤ := by
      rw [hW.1.1.2 x hW.2.1]; exact ENat.natCast_ne_top _
    exact (Set.encard_ne_top_iff.1 this).to_subtype
  have hm : ∀ θ, MetrizableSpace (P θ) := by
    intro θ
    let t := tripleOf hd hW θ
    let h : P θ → uSet hd t := fun z => ⟨z.1.1, z.2⟩
    have hh : Topology.IsEmbedding h := by
      rw [← Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal]
      exact (Topology.IsEmbedding.subtypeVal (p := (· ∈ Y))).comp
        (Topology.IsEmbedding.subtypeVal (p := (· ∈ P θ)))
    exact (Topology.IsEmbedding.subtypeVal.comp
      ((isOpenEmbedding_phi hd t).isEmbedding.comp hh)).metrizableSpace
  refine metrizableSpace_of_partition P hPo (fun θ y => if y ∈ P θ then 1 else 0) (fun θ => ?_)
    (fun θ y => by split_ifs <;> norm_num) (fun θ => ?_)
    (locallyFinite_of_finite _) fun y => ?_
  · refine Continuous.if (fun a ha => ?_) continuous_const continuous_const
    rw [ofPred_mem_eq, (isClopen_iff_frontier_eq_empty.1 ⟨hPc θ, hPo θ⟩)] at ha
    exact absurd ha (notMem_empty a)
  · refine closure_minimal (fun y hy => ?_) (hPc θ)
    by_contra h
    exact hy (by simp only [if_neg h])
  · obtain ⟨θ, hθ⟩ := hcov y
    exact ⟨θ, by simp only [if_pos hθ]; norm_num⟩

/-- **2021 Proposition 2.7.16**: for `X` metrizable, the topology `T_{bX}` is metrizable.  (The
text: Hausdorff, locally metrizable and paracompact, then Nagata–Smirnov; here `B⁻¹(W)` is
metrizable for every centred `W ∈ N_{X,x}`, and Smirnov's theorem in the pulled-back form
`metrizableSpace_of_pullback` along the continuous `B` into the paracompact `X` replaces the
paracompactness argument.) -/
theorem proposition_2_7_16 [MetrizableSpace X] : MetrizableSpace (BSpace hd) := by
  have : ParacompactSpace X := paracompactSpace_of_metrizableSpace X
  refine metrizableSpace_of_pullback (bMap hd) (continuous_bMap hd) fun x => ?_
  obtain ⟨V, hV⟩ := faceStructuredNbhdsAt_nonempty hd x
  have hW := reach_mem_faceStructuredNbhdsAt hd hV
  exact ⟨reach d V x, hW.1.1.1, hW.2.1,
    metrizableSpace_preimage hd hW (isCenteredAt_reach hd hV.1.1.1 hV.2.1)⟩

instance [MetrizableSpace X] : MetrizableSpace (BSpace hd) := proposition_2_7_16 hd

/-- **2021 Theorem 2.7.13 (1)**, with the characterization of its last paragraph (topological
part): `bX` carries the metrizable topology `T_{bX}`, for which every `U(x, V, θ)` is open, every
`Φ_{(x,V,θ)}` is an open embedding into `θ` (a homeomorphism onto `θ` for `V` centred at `x`), and
it is the only topology with these properties; `B : bX → X` is continuous, with image `∂X` and
fibres of `d(x)` points. -/
theorem theorem_2_7_13_topology [MetrizableSpace X] :
    MetrizableSpace (BSpace hd) ∧ (∀ t, IsOpen (uSet hd t)) ∧
      (∀ t, Topology.IsOpenEmbedding (phi hd t)) ∧
      (∀ τ : TopologicalSpace (BSpace hd), (∀ t, IsOpen[τ] (uSet hd t)) →
        (∀ t U, IsOpen[τ] U → ∃ N, IsOpen N ∧ bMap hd '' (U ∩ uSet hd t) = N ∩ t.θ) →
          τ = bTopology hd) ∧
      Continuous (bMap hd) ∧ range (bMap hd) = {x | 1 ≤ d x} ∧
      ∀ x, (bMap hd ⁻¹' {x}).encard = d x :=
  ⟨proposition_2_7_16 hd, isOpen_uSet hd, isOpenEmbedding_phi hd, eq_of_isOpen_uSet hd,
    continuous_bMap hd, range_bMap hd, encard_bMap_preimage hd⟩

end Metrizable
end TameBoundary

/-! ### Tame M-polyfolds -/

namespace MPolyfold

open TameBoundary TopologicalSpace

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **2021 Lemma 2.7.15, p. 85** (new in the 2021 edition): for a tame `X`, the sets of `T_{bX}`
(`IsBOpen`) are the open sets of a topology on `bX`. -/
theorem lemma_2_7_15_2021 (hP : P.IsTame) :
    ∃ τ : TopologicalSpace (P.TameBoundarySpace hP),
      ∀ U, IsOpen[τ] U ↔ IsBOpen (P.isCornerIndex_degIndex hP) U :=
  lemma_2_7_15 _

/-- **2021 Proposition 2.7.12, p. 83** (new in the 2021 edition), topological part: for two
triples, `Φ(U(x, V, θ) ∩ U(x', V', θ'))` is open in `θ` and in `θ'`, and the transition map is the
identity on the underlying points (each `Φ` being an open embedding, `isOpenEmbedding_phi`). -/
theorem proposition_2_7_12_2021 (hP : P.IsTame) (t t' : BTriple (P.isCornerIndex_degIndex hP)) :
    (∃ N, IsOpen N ∧ bMap _ '' (uSet _ t ∩ uSet _ t') = N ∩ t.θ) ∧
      (∃ N', IsOpen N' ∧ bMap _ '' (uSet _ t ∩ uSet _ t') = N' ∩ t'.θ) ∧
      ∀ p (h : p ∈ uSet _ t ∩ uSet _ t'),
        (phi _ t' ⟨p, h.2⟩ : X) = (phi _ t ⟨p, h.1⟩ : X) :=
  proposition_2_7_12 _ t t'

/-- **2021 Proposition 2.7.16, p. 85** (new in the 2021 edition): `T_{bX}` is Hausdorff and
metrizable. -/
theorem proposition_2_7_16_2021 (hP : P.IsTame) :
    T2Space (P.TameBoundarySpace hP) ∧ MetrizableSpace (P.TameBoundarySpace hP) := by
  have := P.metrizableSpace
  exact ⟨inferInstance, proposition_2_7_16 _⟩

/-- **2021 Theorem 2.7.13, pp. 83–84** (new in the 2021 edition), the topological part:
(1) `bX` carries the metrizable topology `T_{bX}`; every `U(x, V, θ)` is open and every
`Φ_{(x,V,θ)}` is an open embedding into `θ` (onto `θ` for `V` centred at `x`); `T_{bX}` is the only
topology with these properties; `B` is continuous with image `∂X`, and every `x` has exactly
`d_X(x)` preimages.  Parts (2), (3) and the sc-statements are not formalized (see the header). -/
theorem theorem_2_7_13_2021 (hP : P.IsTame) :
    MetrizableSpace (P.TameBoundarySpace hP) ∧
      (∀ t, IsOpen (uSet (P.isCornerIndex_degIndex hP) t)) ∧
      (∀ t, Topology.IsOpenEmbedding (phi (P.isCornerIndex_degIndex hP) t)) ∧
      (∀ τ : TopologicalSpace (P.TameBoundarySpace hP),
        (∀ t, IsOpen[τ] (uSet (P.isCornerIndex_degIndex hP) t)) →
          (∀ t U, IsOpen[τ] U → ∃ N, IsOpen N ∧
            bMap (P.isCornerIndex_degIndex hP) '' (U ∩ uSet _ t) = N ∩ t.θ) →
            τ = bTopology (P.isCornerIndex_degIndex hP)) ∧
      Continuous (P.tameBoundaryMap hP) ∧ range (P.tameBoundaryMap hP) = P.boundary ∧
      ∀ x, (P.tameBoundaryMap hP ⁻¹' {x}).encard = P.degIndex x := by
  have := P.metrizableSpace
  exact theorem_2_7_13_topology _

/-- **2021 Definition 2.7.14, p. 84** (new in the 2021 edition), topological part: the **tame
boundary** of the tame `X` is `B : bX → X`, `[x, V, θ] ↦ x`, here as a continuous map (its image
is `∂X`, `range_tameBoundaryMap`).  The M-polyfold structure of `bX` (Theorem 2.7.13 (2)) is not
formalized. -/
def tameBoundary (hP : P.IsTame) : C(P.TameBoundarySpace hP, X) :=
  ⟨P.tameBoundaryMap hP, continuous_bMap _⟩

@[simp] lemma tameBoundary_apply (hP : P.IsTame) (p : P.TameBoundarySpace hP) :
    P.tameBoundary hP p = P.tameBoundaryMap hP p := rfl

end MPolyfold

end Polyfold
