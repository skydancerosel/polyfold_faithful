import Polyfold.Chapter17.TameBoundaryTransitionStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.4 (pp. 802–809): **the topology of `|bC|`**, Definition 17.4.17 – Proposition 17.4.25.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `BOrbit hT hS` (`|bC|`), `faceImageOn` (`|Ψ_θ(A ∩ θ)|`), `exists_faceObj_center_eq` (every object
  of `bC` is some `Ψ_θ(ō)`), `GoodNbhd.exists_nhds_π_eq` (the local sc-diffeomorphism `f̄` of
  p. 802 on the level of `|bC|`, from Lemma 17.4.13).
* **Definition 17.4.17**: `IsBdryOpen` (as we read it), `IsBdryOpenLiteral` (as printed), the
  topology `bdryTopology`; `IsBdryOpen.exists_nhds`.
* **Lemma 17.4.18**: `lemma_17_4_18`, `isOpen_faceImageOn`; `not_isBdryOpenLiteral_empty`,
  `lemma_17_4_18_literal`.
* **Lemma 17.4.20**: `GoodNbhd.lemma_17_4_20` (`|Ψ_θ| : G_θ \ θ → |bC|` is an open embedding),
  `range_faceFunctor_orbitMap`, `isOpen_faceImage`, `metrizableSpace_faceOrbitSpace`,
  `metrizableSpace_faceImage`.
* **Corollary 17.4.21**: `corollary_17_4_21`.
* **(17.76)** `bdrySigma` (`σ`) and **Lemma 17.4.22** (`continuous_bdrySigma`,
  `isClosedMap_bdrySigma`, `lemma_17_4_22`).
* **Theorem 17.4.19**: `metrizableSpace_bdryOrbit`, `theorem_17_4_19`; the ingredients (17.79)
  `GoodNbhd.exists_mem_faceImage`, `GoodNbhd.metrizableSpace_bdrySigma_preimage`,
  `isEmpty_bdrySigma_preimage_compl`, and `metrizableSpace_of_isOpen_cover`.
* **Propositions 17.4.23–17.4.25**: `proposition_17_4_23`, `proposition_17_4_24`,
  `proposition_17_4_25` (consequences of metrizability).

## Readings

* **Definition 17.4.17.** The condition is printed "for every element `z ∈ |bC|`"; we read
  "for every `z ∈ Q`", as the proof of Lemma 17.4.18 does ("Clearly `∅` and `|bC|` belong to our
  collection", "say `z ∈ Q ∩ Q'`").  With `z ∈ |bC|` taken literally, `∅` would not be open
  (`lemma_17_4_18_literal`). "Open `A(ō) ⊂ θ`" is taken as `A ∩ θ` with `A` open in `O`.
* The representatives are the `Ψ_θ(ō) = [α, Ψ, U(ō), θ]` (`faceObj_center`).
* **Theorem 17.4.19.** "A homeomorphism onto an open subset of `|C|`": we read `|bC|` for `|C|`,
  as in the clause that follows ("`|Ψ_θ(θ)|` is open in `|bC|`").
* Lemma 17.4.20 and everything depending on it use the standing hypotheses of the face
  uniformizers: `Ψ̂` continuous (`S.HatContinuous`) and `G` fixing `ō` (`Ψ.1.FixesPoint o`,
  supplied for every uniformizer by `S.IsCentred`). These are met by the quadrant polyfold
  (`quadrant_hatContinuous`, `quadrant_isCentred`).
* The metrizability is obtained as in the proof of Proposition 17.4.25 (pp. 807–809): `σ` is
  continuous into the metrizable `|C|`, and every point of `|C|` has a neighbourhood with
  metrizable `σ`-preimage, a finite disjoint union of the `|Ψ_θ(θ)|` (17.79), or empty off `|∂C|`;
  Smirnov's theorem in its pulled-back form (`metrizableSpace_of_pullback`) then applies.
  Propositions 17.4.23–17.4.25 follow.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter TopologicalSpace

noncomputable section

universe u

namespace Polyfold

open TameBoundary

/-- A space covered by open metrizable sets any two of which are equal or disjoint is
metrizable (the finite disjoint union `⊔_i |Ψ_i(θ_i)|` of (17.79)). -/
theorem metrizableSpace_of_isOpen_cover {Y : Type*} [TopologicalSpace Y] (F : Set (Set Y))
    (hcov : ∀ y, ∃ E ∈ F, y ∈ E) (hopen : ∀ E ∈ F, IsOpen E)
    (hdisj : ∀ E ∈ F, ∀ E' ∈ F, ∀ y ∈ E, y ∈ E' → E = E')
    (hmet : ∀ E ∈ F, MetrizableSpace E) : MetrizableSpace Y := by
  classical
  let _ : TopologicalSpace F := ⊥
  have : DiscreteTopology F := ⟨rfl⟩
  have : ParacompactSpace F := paracompactSpace_of_metrizableSpace F
  choose τ hτF hτy using hcov
  let τ' : Y → F := fun y => ⟨τ y, hτF y⟩
  have hτ : ∀ E ∈ F, ∀ y ∈ E, τ y = E := fun E hE y hy => hdisj _ (hτF y) _ hE y (hτy y) hy
  have hpre : ∀ E : F, τ' ⁻¹' {E} = E.1 := by
    intro E
    ext y
    constructor
    · intro h
      have : τ y = E.1 := congrArg Subtype.val h
      rw [← this]; exact hτy y
    · intro hy
      exact Subtype.ext (hτ _ E.2 y hy)
  refine metrizableSpace_of_pullback τ' ?_ fun E => ⟨{E}, isOpen_discrete _, rfl, ?_⟩
  · refine continuous_def.2 fun T _ => ?_
    have : τ' ⁻¹' T = ⋃ E ∈ T, E.1 := by
      ext y
      simp only [mem_preimage, mem_iUnion]
      constructor
      · intro h; exact ⟨τ' y, h, hτy y⟩
      · rintro ⟨E, hE, hy⟩
        have : τ' y = E := Subtype.ext (hτ _ E.2 y hy)
        rw [this]; exact hE
    rw [this]
    exact isOpen_biUnion fun E _ => hopen E.1 E.2
  · have := hmet E.1 E.2
    exact (Homeomorph.setCongr (hpre E)).isEmbedding.metrizableSpace

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {hT : S.IsTame} {hS : S.HasUniformizers}

/-- `|bC|`, the orbit space of the tame boundary category. -/
abbrev BOrbit (hT : S.IsTame) (hS : S.HasUniformizers) : Type u :=
  (S.bdryGroupoid hT hS).OrbitSpace

namespace GoodNbhd

variable {Ψ Ψ' : S.Unif} {o : Ψ.1.O} {o' : Ψ'.1.O} (V : S.GoodNbhd Ψ o) (V' : S.GoodNbhd Ψ' o')

/-- If `Ψ_θ(x)` and `Ψ'_{θ'}(x')` are isomorphic in `bC`, some `h ∈ M(Ψ, Ψ')*_{θ,θ'}` runs from
`x` to `x'`. -/
theorem exists_mem_transFaceSet_of_π_eq {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) {x : Ψ.1.O} (hx : x ∈ θ) {x' : Ψ'.1.O} (hx' : x' ∈ θ')
    (h : (S.bdryGroupoid hT hS).π (V.faceObj hT hS hθ x hx) =
      (S.bdryGroupoid hT hS).π (V'.faceObj hT hS hθ' x' hx')) :
    ∃ a ∈ V.transFaceSet hT V' hθ hθ', a.src = x ∧ a.tgt = x' := by
  obtain ⟨Φ, hs, ht⟩ := ((S.bdryGroupoid hT hS).π_eq_π_iff).1 h
  let hb : V.FaceTr hT hS V' hθ hθ' := ⟨⟨x, hx⟩, Φ, ⟨x', hx'⟩, hs, ht⟩
  refine ⟨V.faceTrToTr V' hb, ?_, rfl, rfl⟩
  rw [← (V.definition_17_4_12 V' (hS := hS) hθ).2.2.2 hθ']
  exact mem_range_self hb

/-- An element of `M(Ψ, Ψ')*_{θ,θ'}` gives an isomorphism `Ψ_θ(x) ≅ Ψ'_{θ'}(x')`. -/
theorem π_eq_of_mem_transFaceSet {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) {a : S.Tr Ψ Ψ'} (ha : a ∈ V.transFaceSet hT V' hθ hθ') :
    (S.bdryGroupoid hT hS).π (V.faceObj hT hS hθ a.src ha.1) =
      (S.bdryGroupoid hT hS).π (V'.faceObj hT hS hθ' a.tgt ha.2.1) := by
  obtain ⟨hx, hx', hl⟩ := ha
  obtain ⟨-, h, hs, ht, -⟩ := (V.lemma_17_4_10 V' (hS := hS) hθ hθ').2 a hx hx' hl
  refine ((S.bdryGroupoid hT hS).π_eq_π_iff).2 ⟨h.mor, ?_, ?_⟩
  · rw [show (S.bdryGroupoid hT hS).src h.mor = _ from h.src_mor, hs]
  · rw [show (S.bdryGroupoid hT hS).tgt h.mor = _ from h.tgt_mor, ht]

/-- **The local form of `M(Ψ_θ, Ψ'_{θ'})`** (the sc-diffeomorphism `f̄` of p. 802): if
`Ψ_θ(x) ≅ Ψ'_{θ'}(x')`, then for every open `A' ∋ x'` there is an open `N ∋ x` such that every
`Ψ_θ(y)`, `y ∈ N ∩ θ`, is isomorphic to some `Ψ'_{θ'}(y')`, `y' ∈ A' ∩ θ'`. -/
theorem exists_nhds_π_eq {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) {x : Ψ.1.O} (hx : x ∈ θ) {x' : Ψ'.1.O} (hx' : x' ∈ θ')
    (h : (S.bdryGroupoid hT hS).π (V.faceObj hT hS hθ x hx) =
      (S.bdryGroupoid hT hS).π (V'.faceObj hT hS hθ' x' hx'))
    {A' : Set Ψ'.1.O} (hA' : IsOpen A') (hxA' : x' ∈ A') :
    ∃ N : Set Ψ.1.O, IsOpen N ∧ x ∈ N ∧ ∀ y (hy : y ∈ θ), y ∈ N →
      ∃ (y' : Ψ'.1.O) (hy' : y' ∈ θ'), y' ∈ A' ∧
        (S.bdryGroupoid hT hS).π (V.faceObj hT hS hθ y hy) =
          (S.bdryGroupoid hT hS).π (V'.faceObj hT hS hθ' y' hy') := by
  obtain ⟨a, ha, rfl, rfl⟩ := V.exists_mem_transFaceSet_of_π_eq V' hθ hθ' hx hx' h
  obtain ⟨T, N, hNo, haN, hNT, hN⟩ := V.exists_isOpen_transFaceSet V' hθ hθ' ha
  have hf := T.isDHomeoOn_germMap
  refine ⟨N ∩ (T.srcSet ∩ T.germMap ⁻¹' A'), hNo.inter
    (hf.continuousOn.isOpen_inter_preimage hf.isOpen hA'), ⟨haN, T.src_mem, ?_⟩, ?_⟩
  · change T.germMap a.src ∈ A'
    rw [T.germMap_src]; exact hxA'
  · rintro y hy ⟨hyN, hyT, hyA⟩
    have hb := hN _ (T.srcInv_mem hyT) (by rw [T.src_srcInv hyT]; exact hyN)
      (by rw [T.src_srcInv hyT]; exact hy)
    refine ⟨(T.srcInv y).tgt, hb.2.1, hyA, ?_⟩
    have := V.π_eq_of_mem_transFaceSet V' (hS := hS) hθ hθ' hb
    rw [← this]
    exact congrArg _ (V.faceObj_congr₂ rfl (T.src_srcInv hyT).symm hθ hθ _ _)

/-- `Ψ_θ(ō)` is the class of the tuple `(α, Ψ, U(ō), θ)`. -/
theorem faceObj_center {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    V.faceObj hT hS hθ o (V.mem_of_mem_faces hθ) = S.ptObj hT hS (V.germ hT hθ) := by
  change S.ptObj hT hS (V.faceGerm hT hθ o _) = _
  rw [V.faceGerm_eq_of_mem hθ (V.mem_of_mem_faces hθ) (q := V.germ hT hθ) (cls_mem_uSet _ _) rfl]

end GoodNbhd

/-- **Every object of `bC` is some `Ψ_θ(ō)`**: the class `[α, Ψ, U(ō), θ]` of a tuple. -/
theorem exists_faceObj_center_eq (a : S.BObj hT hS) :
    ∃ (Ψ : S.Unif) (o : Ψ.1.O) (V : S.GoodNbhd Ψ o) (θ : Set Ψ.1.O) (hθ : θ ∈ V.faces),
      V.faceObj hT hS hθ o (V.mem_of_mem_faces hθ) = a := by
  obtain ⟨t, rfl⟩ := BdryTuple.toBObj_surjective (S := S) (hT := hT) (hS := hS) a
  exact ⟨t.unif, t.o, t.V, t.θ, t.face, by rw [GoodNbhd.faceObj_center, BdryTuple.toBObj_eq_ptObj]⟩

variable (hT hS) in
/-- `|Ψ_θ(A)| = {|Ψ_θ(x)| : x ∈ A ∩ θ}` for `A ⊆ O`. -/
def faceImageOn {Ψ : S.Unif} {o : Ψ.1.O} (V : S.GoodNbhd Ψ o) {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces)
    (A : Set Ψ.1.O) : Set (BOrbit hT hS) :=
  {z | ∃ (x : Ψ.1.O) (hx : x ∈ θ), x ∈ A ∧ (S.bdryGroupoid hT hS).π (V.faceObj hT hS hθ x hx) = z}

variable (hT hS) in
/-- **2021 Definition 17.4.17, p. 802**, as we read it: `Q ⊆ |bC|` is **open** if every `z ∈ Q`
has a representative `Ψ_θ(ō) = [α, Ψ, U(ō), θ]` and an open `A ∋ ō` with `|Ψ_θ(A ∩ θ)| ⊆ Q`
(`A` open in `O`, so `A ∩ θ` is an open neighbourhood of `ō` in `θ`).  The text quantifies over
every `z ∈ |bC|`; we read `z ∈ Q` (`IsBdryOpenLiteral`, `lemma_17_4_18_literal`). -/
def IsBdryOpen (Q : Set (BOrbit hT hS)) : Prop :=
  ∀ z ∈ Q, ∃ (Ψ : S.Unif) (o : Ψ.1.O) (V : S.GoodNbhd Ψ o) (θ : Set Ψ.1.O) (hθ : θ ∈ V.faces),
    (S.bdryGroupoid hT hS).π (V.faceObj hT hS hθ o (V.mem_of_mem_faces hθ)) = z ∧
    ∃ A : Set Ψ.1.O, IsOpen A ∧ o ∈ A ∧ faceImageOn hT hS V hθ A ⊆ Q

variable (hT hS) in
/-- **2021 Definition 17.4.17 as printed**: the condition is required for every `z ∈ |bC|`. -/
def IsBdryOpenLiteral (Q : Set (BOrbit hT hS)) : Prop :=
  ∀ z : BOrbit hT hS, ∃ (Ψ : S.Unif) (o : Ψ.1.O) (V : S.GoodNbhd Ψ o) (θ : Set Ψ.1.O)
    (hθ : θ ∈ V.faces),
    (S.bdryGroupoid hT hS).π (V.faceObj hT hS hθ o (V.mem_of_mem_faces hθ)) = z ∧
    ∃ A : Set Ψ.1.O, IsOpen A ∧ o ∈ A ∧ faceImageOn hT hS V hθ A ⊆ Q

/-- **Openness at every point of a face** (p. 802): if `Q` is open and `|Ψ_θ(x)| ∈ Q`, then
`|Ψ_θ(N ∩ θ)| ⊆ Q` for an open `N ∋ x`. -/
theorem IsBdryOpen.exists_nhds {Q : Set (BOrbit hT hS)} (hQ : IsBdryOpen hT hS Q) {Ψ : S.Unif}
    {o : Ψ.1.O} (V : S.GoodNbhd Ψ o) {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) {x : Ψ.1.O}
    (hx : x ∈ θ) (hxQ : (S.bdryGroupoid hT hS).π (V.faceObj hT hS hθ x hx) ∈ Q) :
    ∃ N : Set Ψ.1.O, IsOpen N ∧ x ∈ N ∧ faceImageOn hT hS V hθ N ⊆ Q := by
  obtain ⟨Ψ', o', V', θ', hθ', hz, A, hA, hoA, hAQ⟩ := hQ _ hxQ
  obtain ⟨N, hN, hxN, hNA⟩ := V.exists_nhds_π_eq V' hθ hθ' hx (V'.mem_of_mem_faces hθ') hz.symm
    hA hoA
  refine ⟨N, hN, hxN, ?_⟩
  rintro _ ⟨y, hy, hyN, rfl⟩
  obtain ⟨y', hy', hy'A, he⟩ := hNA y hy hyN
  rw [he]
  exact hAQ ⟨y', hy', hy'A, rfl⟩

/-- **The topology `T_bC` on `|bC|`** (2021 Definition 17.4.17 and Lemma 17.4.18). -/
instance bdryTopology (hT : S.IsTame) (hS : S.HasUniformizers) :
    TopologicalSpace (BOrbit hT hS) where
  IsOpen := IsBdryOpen hT hS
  isOpen_univ z _ := by
    induction z using Quotient.inductionOn with
    | h a =>
      obtain ⟨Ψ, o, V, θ, hθ, he⟩ := exists_faceObj_center_eq a
      exact ⟨Ψ, o, V, θ, hθ, by rw [he]; rfl, univ, isOpen_univ, mem_univ _,
        subset_univ _⟩
  isOpen_inter Q Q' hQ hQ' z hz := by
    obtain ⟨Ψ, o, V, θ, hθ, he, A, hA, hoA, hAQ⟩ := hQ z hz.1
    obtain ⟨N, hN, hoN, hNQ⟩ := hQ'.exists_nhds V hθ (V.mem_of_mem_faces hθ) (he ▸ hz.2)
    refine ⟨Ψ, o, V, θ, hθ, he, A ∩ N, hA.inter hN, ⟨hoA, hoN⟩, ?_⟩
    rintro _ ⟨x, hx, hxAN, rfl⟩
    exact ⟨hAQ ⟨x, hx, hxAN.1, rfl⟩, hNQ ⟨x, hx, hxAN.2, rfl⟩⟩
  isOpen_sUnion F hF z hz := by
    obtain ⟨Q, hQF, hzQ⟩ := hz
    obtain ⟨Ψ, o, V, θ, hθ, he, A, hA, hoA, hAQ⟩ := hF Q hQF z hzQ
    exact ⟨Ψ, o, V, θ, hθ, he, A, hA, hoA, hAQ.trans (subset_sUnion_of_mem hQF)⟩

theorem isOpen_bdry_iff {Q : Set (BOrbit hT hS)} : IsOpen Q ↔ IsBdryOpen hT hS Q := Iff.rfl

/-- The sets `|Ψ_θ(A ∩ θ)|`, `A ⊆ O` open, are open (2021 p. 803). -/
theorem isOpen_faceImageOn {Ψ : S.Unif} {o : Ψ.1.O} (V : S.GoodNbhd Ψ o) {θ : Set Ψ.1.O}
    (hθ : θ ∈ V.faces) {A : Set Ψ.1.O} (hA : IsOpen A) :
    IsOpen (faceImageOn hT hS V hθ A) := by
  rintro _ ⟨x, hx, hxA, rfl⟩
  obtain ⟨Ψ', o', V', θ', hθ', he⟩ := exists_faceObj_center_eq (V.faceObj hT hS hθ x hx)
  obtain ⟨N, hN, hoN, hNA⟩ := V'.exists_nhds_π_eq V hθ' hθ (V'.mem_of_mem_faces hθ') hx
    (congrArg _ he) hA hxA
  refine ⟨Ψ', o', V', θ', hθ', by rw [he], N, hN, hoN, ?_⟩
  rintro _ ⟨y, hy, hyN, rfl⟩
  obtain ⟨y', hy', hy'A, hπ⟩ := hNA y hy hyN
  exact ⟨y', hy', hy'A, hπ.symm⟩

variable (hT hS) in
/-- **2021 Lemma 17.4.18, p. 803**: `T_bC` (Definition 17.4.17, read with `z ∈ Q`) is a topology
on `|bC|`, and every `|Ψ_θ(A)|` with `A ⊆ θ` open is open. -/
theorem lemma_17_4_18 :
    (∀ Q : Set (BOrbit hT hS), IsOpen Q ↔ IsBdryOpen hT hS Q) ∧
    ∀ {Ψ : S.Unif} {o : Ψ.1.O} (V : S.GoodNbhd Ψ o) {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces)
      {A : Set Ψ.1.O}, IsOpen A → IsOpen (faceImageOn hT hS V hθ A) :=
  ⟨fun _ => Iff.rfl, @fun _ _ V _ hθ _ hA => isOpen_faceImageOn V hθ hA⟩

/-- **Definition 17.4.17 as printed admits no empty open set** when `bC` has an object: the
condition at a point `z ∉ Q = ∅` cannot hold. -/
theorem not_isBdryOpenLiteral_empty (a : S.BObj hT hS) : ¬ IsBdryOpenLiteral hT hS ∅ := by
  intro h
  obtain ⟨Ψ, o, V, θ, hθ, -, A, -, hoA, hAQ⟩ := h ((S.bdryGroupoid hT hS).π a)
  exact hAQ ⟨o, V.mem_of_mem_faces hθ, hoA, rfl⟩


/-! ### Lemma 17.4.20 and local metrizability -/

namespace GoodNbhd

variable {Ψ : S.Unif} {o : Ψ.1.O} (V : S.GoodNbhd Ψ o)

/-- `|Ψ_θ(θ)| = |Ψ_θ(O ∩ θ)|`. -/
theorem faceImage_eq_faceImageOn {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    V.faceImage hT hS hθ = faceImageOn hT hS V hθ univ := by
  ext z
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, mem_univ _, h⟩, fun ⟨x, hx, _, h⟩ => ⟨x, hx, h⟩⟩

/-- `|Ψ_θ(θ)|` is open in `|bC|`. -/
theorem isOpen_faceImage {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) : IsOpen (V.faceImage hT hS hθ) := by
  rw [V.faceImage_eq_faceImageOn]; exact isOpen_faceImageOn V hθ isOpen_univ

variable (hT) in
/-- `G_θ` acts on the face `θ` by sc-diffeomorphisms. -/
theorem isScSmoothMap_faceStabilizer_smul {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces)
    (g : faceStabilizer Ψ θ) :
    (V.faceSubPolyfold hT hθ).IsScSmoothMap (V.faceSubPolyfold hT hθ) fun y : θ => g • y :=
  MPolyfold.isScSmoothOn_subPolyfold_of_val _
    ((Ψ.1.smooth_smul g.1).comp (MPolyfold.subPolyfold_inclusion_isScSmooth _))

/-- `G_θ \ θ` is metrizable (2021 Corollary 17.4.21: "`θ` is metrizable", Definition 17.1.2). -/
theorem metrizableSpace_faceOrbitSpace (hT : S.IsTame) {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    MetrizableSpace (GroupoidStr.translation (faceStabilizer Ψ θ) θ).OrbitSpace :=
  metrizableSpace_translation_orbitSpace (V.isScSmoothMap_faceStabilizer_smul hT hθ)

variable (hT hS) in
/-- **2021 Lemma 17.4.20, p. 803**: `Ψ_θ : G_θ ⋉ θ → bC`, passing to orbit spaces, is a
homeomorphism `|Ψ_θ| : G_θ \ θ → |Ψ_θ(θ)|` onto an open subset of `|bC|`. -/
theorem lemma_17_4_20 (hc : S.HatContinuous) (hfix : Ψ.1.FixesPoint o) {θ : Set Ψ.1.O}
    (hθ : θ ∈ V.faces) : IsOpenEmbedding (V.faceFunctor hT hS hc hfix hθ).orbitMap := by
  set f := (V.faceFunctor hT hS hc hfix hθ).orbitMap
  have hfm : ∀ x : θ, f ((GroupoidStr.translation (faceStabilizer Ψ θ) θ).π x) =
      (S.bdryGroupoid hT hS).π (V.faceObj hT hS hθ x.1 x.2) := fun _ => rfl
  have hcont : Continuous fun x : θ => (S.bdryGroupoid hT hS).π (V.faceObj hT hS hθ x.1 x.2) := by
    refine continuous_def.2 fun Q hQ => isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨N, hN, hxN, hNQ⟩ := IsBdryOpen.exists_nhds hQ V hθ x.2 hx
    exact ⟨Subtype.val ⁻¹' N, fun y hy => hNQ ⟨y.1, y.2, hy, rfl⟩,
      hN.preimage continuous_subtype_val, hxN⟩
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact isQuotientMap_quotient_mk'.continuous_iff.2 hcont
  · intro w w' h
    induction w using Quotient.inductionOn with | h x => ?_
    induction w' using Quotient.inductionOn with | h y => ?_
    obtain ⟨Φ, hs, ht⟩ := ((S.bdryGroupoid hT hS).π_eq_π_iff).1 h
    obtain ⟨m, hms, hmt, -⟩ := (GroupoidFunctor.full_iff _).1 (V.lemma_17_4_6 hc hfix hθ).2.1
      x y Φ hs ht
    exact ((GroupoidStr.translation (faceStabilizer Ψ θ) θ).π_eq_π_iff).2 ⟨m, hms, hmt⟩
  · intro W hW
    have hW' : IsOpen ((GroupoidStr.translation (faceStabilizer Ψ θ) θ).π ⁻¹' W) := hW
    obtain ⟨A, hA, hAe⟩ := isOpen_induced_iff.1 hW'
    have he : f '' W = faceImageOn hT hS V hθ A := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        induction w using Quotient.inductionOn with
        | h x =>
          have hx : x ∈ Subtype.val ⁻¹' A := by rw [hAe]; exact hw
          exact ⟨x.1, x.2, hx, rfl⟩
      · rintro ⟨x, hx, hxA, rfl⟩
        have hx' : (⟨x, hx⟩ : θ) ∈ (GroupoidStr.translation (faceStabilizer Ψ θ) θ).π ⁻¹' W := by
          rw [← hAe]; exact hxA
        exact ⟨_, hx', rfl⟩
    rw [he]
    exact isOpen_faceImageOn V hθ hA

theorem range_faceFunctor_orbitMap (hc : S.HatContinuous) (hfix : Ψ.1.FixesPoint o)
    {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    range (V.faceFunctor hT hS hc hfix hθ).orbitMap = V.faceImage hT hS hθ := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    induction w using Quotient.inductionOn with
    | h x => exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(GroupoidStr.translation (faceStabilizer Ψ θ) θ).π ⟨x, hx⟩, rfl⟩

/-- `|Ψ_θ(θ)|` is metrizable (it is homeomorphic to `G_θ \ θ`). -/
theorem metrizableSpace_faceImage (hc : S.HatContinuous) (hfix : Ψ.1.FixesPoint o)
    {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) : MetrizableSpace (V.faceImage hT hS hθ) := by
  have := V.metrizableSpace_faceOrbitSpace hT hθ
  have h := (V.lemma_17_4_20 hT hS hc hfix hθ).isEmbedding
  have e := h.toHomeomorph
  rw [V.range_faceFunctor_orbitMap hc hfix hθ] at e
  exact e.symm.isEmbedding.metrizableSpace

end GoodNbhd

/-- With centred uniformizers, every object of `bC` is some `Ψ_θ(ō)` with `G` fixing `ō`. -/
theorem exists_faceObj_center_eq_of_isCentred (hcent : S.IsCentred) (a : S.BObj hT hS) :
    ∃ (Ψ : S.Unif) (o : Ψ.1.O) (V : S.GoodNbhd Ψ o) (θ : Set Ψ.1.O) (hθ : θ ∈ V.faces),
      Ψ.1.FixesPoint o ∧ V.faceObj hT hS hθ o (V.mem_of_mem_faces hθ) = a := by
  obtain ⟨t, rfl⟩ := BdryTuple.toBObj_surjective (S := S) (hT := hT) (hS := hS) a
  exact ⟨t.unif, t.o, t.V, t.θ, t.face, hcent.fixesPoint t.mem t.obj_o,
    by rw [GoodNbhd.faceObj_center, BdryTuple.toBObj_eq_ptObj]⟩

/-- **2021 Corollary 17.4.21, p. 804**: `|bC|` is locally metrizable. -/
theorem corollary_17_4_21 (hc : S.HatContinuous) (hcent : S.IsCentred) (z : BOrbit hT hS) :
    ∃ U : Set (BOrbit hT hS), IsOpen U ∧ z ∈ U ∧ MetrizableSpace U := by
  induction z using Quotient.inductionOn with
  | h a =>
    obtain ⟨Ψ, o, V, θ, hθ, hfix, he⟩ := exists_faceObj_center_eq_of_isCentred hcent a
    exact ⟨V.faceImage hT hS hθ, V.isOpen_faceImage hθ, ⟨o, V.mem_of_mem_faces hθ, by rw [he]; rfl⟩,
      V.metrizableSpace_faceImage hc hfix hθ⟩

/-! ### The forgetful map `σ` -/

variable (hT hS) in
/-- **(17.76)**: `σ : |bC| → |∂C| ⊆ |C|`, `|[α, Ψ, U(ō), θ]| ↦ |α|` (`|B_C|`). -/
def bdrySigma : BOrbit hT hS → C.toGroupoidStr.OrbitSpace := (S.bdryFunctorC hT hS).orbitMap

@[simp] theorem bdrySigma_π (a : S.BObj hT hS) :
    S.bdrySigma hT hS ((S.bdryGroupoid hT hS).π a) = C.toGroupoidStr.π a.α := rfl

/-- **2021 Lemma 17.4.22, p. 804 (continuity)**: `σ` is continuous. -/
theorem continuous_bdrySigma : Continuous (S.bdrySigma hT hS) := by
  refine continuous_def.2 fun Q hQ z hz => ?_
  induction z using Quotient.inductionOn with
  | h a =>
    obtain ⟨Ψ, o, V, θ, hθ, he⟩ := exists_faceObj_center_eq a
    have hA : IsOpen ((fun q : Ψ.1.O => C.toGroupoidStr.π (Ψ.1.obj q)) ⁻¹' Q) :=
      hQ.preimage Ψ.1.continuous_π_obj
    refine ⟨Ψ, o, V, θ, hθ, by rw [he]; rfl, _, hA, ?_, ?_⟩
    · change C.toGroupoidStr.π (Ψ.1.obj o) ∈ Q
      have : S.bdrySigma hT hS ((S.bdryGroupoid hT hS).π a) ∈ Q := hz
      rw [← he, bdrySigma_π, GoodNbhd.faceObj_α] at this
      exact this
    · rintro _ ⟨x, hx, hxA, rfl⟩
      change S.bdrySigma hT hS ((S.bdryGroupoid hT hS).π _) ∈ Q
      rw [bdrySigma_π, GoodNbhd.faceObj_α]
      exact hxA

/-- An object of `bC` over `|Ψ(x)|` forces `x ∈ ∂O`. -/
theorem mem_boundary_of_bdrySigma_eq {Ψ : S.Unif} {x : Ψ.1.O} (a : S.BObj hT hS)
    (h : C.toGroupoidStr.π (Ψ.1.obj x) = C.toGroupoidStr.π a.α) : x ∈ Ψ.1.P.boundary := by
  have hi := (C.toGroupoidStr.π_eq_π_iff).1 h
  change 1 ≤ Ψ.1.P.degIndex x
  rw [← degIndex_eq Ψ hi]
  exact a.mem_boundarySet

namespace GoodNbhd

variable {Ψ : S.Unif} {o : Ψ.1.O} (V : S.GoodNbhd Ψ o)

/-- **(17.79)**: every point of `σ⁻¹(|Ψ(U(ō))|)` lies in some `|Ψ_θ(θ)|`. -/
theorem exists_mem_faceImage (hc : S.HatContinuous) (hfix : Ψ.1.FixesPoint o)
    {z : BOrbit hT hS}
    (hz : S.bdrySigma hT hS z ∈ (fun q : Ψ.1.O => C.toGroupoidStr.π (Ψ.1.obj q)) '' V.1.U) :
    ∃ (θ : Set Ψ.1.O) (hθ : θ ∈ V.faces), z ∈ V.faceImage hT hS hθ := by
  induction z using Quotient.inductionOn with
  | h a =>
    obtain ⟨x, hxU, hx⟩ := hz
    have hxb := mem_boundary_of_bdrySigma_eq a hx
    have hz' : (S.bdryGroupoid hT hS).π a ∈ (S.bdryFunctorC hT hS).orbitMap ⁻¹'
        (C.toGroupoidStr.π '' (Ψ.1.obj '' V.bdry)) :=
      ⟨Ψ.1.obj x, ⟨x, ⟨hxU, hxb⟩, rfl⟩, hx⟩
    rw [← V.display_17_68 hc hfix] at hz'
    obtain ⟨w, hw⟩ := hz'
    induction w using Quotient.inductionOn with
    | h q => exact ⟨q.1.2, q.2.1, q.1.1, q.2.2, hw⟩

/-- **(17.79)–(17.80)**: `σ⁻¹(|Ψ(U(ō))|)` is metrizable (a disjoint union of the open metrizable
`|Ψ_θ(θ)|`, Lemma 17.4.8). -/
theorem metrizableSpace_bdrySigma_preimage (hc : S.HatContinuous) (hfix : Ψ.1.FixesPoint o) :
    MetrizableSpace (S.bdrySigma hT hS ⁻¹'
      ((fun q : Ψ.1.O => C.toGroupoidStr.π (Ψ.1.obj q)) '' V.1.U)) := by
  set Y := S.bdrySigma hT hS ⁻¹' ((fun q : Ψ.1.O => C.toGroupoidStr.π (Ψ.1.obj q)) '' V.1.U)
  refine metrizableSpace_of_isOpen_cover
    {E | ∃ (θ : Set Ψ.1.O) (hθ : θ ∈ V.faces), E = Subtype.val ⁻¹' V.faceImage hT hS hθ}
    (fun y => ?_) ?_ ?_ ?_
  · obtain ⟨θ, hθ, hy⟩ := V.exists_mem_faceImage hc hfix y.2
    exact ⟨_, ⟨θ, hθ, rfl⟩, hy⟩
  · rintro _ ⟨θ, hθ, rfl⟩
    exact (V.isOpen_faceImage hθ).preimage continuous_subtype_val
  · rintro _ ⟨θ, hθ, rfl⟩ _ ⟨θ', hθ', rfl⟩ y hy hy'
    rcases (V.lemma_17_4_8 hc hfix hθ hθ').1 with h | h
    · rw [h]
    · exact absurd (h.le_bot ⟨hy, hy'⟩) (by simp)
  · rintro _ ⟨θ, hθ, rfl⟩
    have := V.metrizableSpace_faceImage (hT := hT) (hS := hS) hc hfix hθ
    have he : IsEmbedding fun y : (Subtype.val ⁻¹' V.faceImage hT hS hθ : Set Y) =>
        (⟨y.1.1, y.2⟩ : V.faceImage hT hS hθ) :=
      (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict _ _
    exact he.metrizableSpace

end GoodNbhd

/-- Away from `∂C` there are no objects of `bC`: `σ⁻¹(|Ψ(O \ ∂O)|) = ∅`. -/
theorem isEmpty_bdrySigma_preimage_compl (Ψ : S.Unif) :
    IsEmpty (S.bdrySigma hT hS ⁻¹'
      ((fun q : Ψ.1.O => C.toGroupoidStr.π (Ψ.1.obj q)) '' (Ψ.1.P.boundary)ᶜ)) := by
  refine ⟨fun ⟨z, hz⟩ => ?_⟩
  induction z using Quotient.inductionOn with
  | h a =>
    obtain ⟨x, hx, he⟩ := hz
    exact hx (mem_boundary_of_bdrySigma_eq a he)

variable (hT hS) in
/-- **2021 Theorem 17.4.19 (metrizability), p. 803**: `(|bC|, T_bC)` is metrizable (the proof of
pp. 806–809: `σ` is continuous into the paracompact Hausdorff `|C|`, and over a neighbourhood
`|Ψ(U(ō))|` of every point of `|∂C|`, resp. `|Ψ(O \ ∂O)|` of every other point, the preimage
`σ⁻¹(·)` is metrizable, resp. empty). -/
theorem metrizableSpace_bdryOrbit (hc : S.HatContinuous) (hcent : S.IsCentred) :
    MetrizableSpace (BOrbit hT hS) := by
  have : ParacompactSpace C.toGroupoidStr.OrbitSpace :=
    paracompactSpace_of_metrizableSpace _
  refine metrizableSpace_of_pullback (S.bdrySigma hT hS) continuous_bdrySigma fun w => ?_
  induction w using Quotient.inductionOn with
  | h β =>
    let Ψ := S.bdryRefUnif hS β
    let o := S.refPt hS β
    have ho : Ψ.1.obj o = β := obj_refPt hS β
    have hfix : Ψ.1.FixesPoint o := hcent.fixesPoint (bdryRefUnif_mem hS β) ho
    by_cases hb : o ∈ Ψ.1.P.boundary
    · obtain ⟨V, -⟩ := exists_goodNbhd (S.isTame_unif hT Ψ) hb isOpen_univ (mem_univ _)
      exact ⟨_, Ψ.1.isOpenMap_π_obj _ V.isOpen, ⟨o, V.mem, congrArg _ ho⟩,
        V.metrizableSpace_bdrySigma_preimage hc hfix⟩
    · have := isEmpty_bdrySigma_preimage_compl (hT := hT) (hS := hS) Ψ
      exact ⟨_, Ψ.1.isOpenMap_π_obj _ Ψ.1.P.isClosed_boundary.isOpen_compl,
        ⟨o, hb, congrArg _ ho⟩, inferInstance⟩

variable (hT hS) in
/-- **2021 Theorem 17.4.19, p. 803**: `(|bC|, T_bC)` is metrizable, and for every representative
`(α, Ψ, U(ō), θ)` (`G` fixing `ō`) `|Ψ_θ(θ)|` is open and `|Ψ_θ| : G_θ \ θ → |Ψ_θ(θ)|` is a
homeomorphism (Lemma 17.4.20). -/
theorem theorem_17_4_19 (hc : S.HatContinuous) (hcent : S.IsCentred) :
    MetrizableSpace (BOrbit hT hS) ∧
    ∀ {Ψ : S.Unif} {o : Ψ.1.O} (V : S.GoodNbhd Ψ o) (hfix : Ψ.1.FixesPoint o)
      {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces),
      IsOpen (V.faceImage hT hS hθ) ∧ IsOpenEmbedding (V.faceFunctor hT hS hc hfix hθ).orbitMap ∧
        range (V.faceFunctor hT hS hc hfix hθ).orbitMap = V.faceImage hT hS hθ :=
  ⟨metrizableSpace_bdryOrbit hT hS hc hcent, fun V hfix _ hθ =>
    ⟨V.isOpen_faceImage hθ, V.lemma_17_4_20 hT hS hc hfix hθ,
      V.range_faceFunctor_orbitMap hc hfix hθ⟩⟩

variable (hT hS) in
/-- **2021 Proposition 17.4.23, p. 805**: `|bC|` is Hausdorff. -/
theorem proposition_17_4_23 (hc : S.HatContinuous) (hcent : S.IsCentred) :
    T2Space (BOrbit hT hS) := by
  have := metrizableSpace_bdryOrbit hT hS hc hcent
  infer_instance

variable (hT hS) in
/-- **2021 Proposition 17.4.24, p. 805**: `|bC|` is regular. -/
theorem proposition_17_4_24 (hc : S.HatContinuous) (hcent : S.IsCentred) :
    RegularSpace (BOrbit hT hS) := by
  have := metrizableSpace_bdryOrbit hT hS hc hcent
  infer_instance

variable (hT hS) in
/-- **2021 Proposition 17.4.25, p. 806**: `|bC|` is paracompact. -/
theorem proposition_17_4_25 (hc : S.HatContinuous) (hcent : S.IsCentred) :
    ParacompactSpace (BOrbit hT hS) := by
  have := metrizableSpace_bdryOrbit hT hS hc hcent
  exact paracompactSpace_of_metrizableSpace _

/-- Points of `O` with the same image in `|C|` lie in one `G`-orbit. -/
theorem exists_smul_eq_of_π_obj_eq {Ψ : S.Unif} {x x' : Ψ.1.O}
    (h : C.toGroupoidStr.π (Ψ.1.obj x) = C.toGroupoidStr.π (Ψ.1.obj x')) :
    ∃ g : Ψ.1.G, g • x = x' := by
  have h' := Ψ.1.isOpenEmbedding_orbitMap.injective
    (a₁ := (GroupoidStr.translation Ψ.1.G Ψ.1.O).π x)
    (a₂ := (GroupoidStr.translation Ψ.1.G Ψ.1.O).π x') h
  obtain ⟨m, hs, ht⟩ := ((GroupoidStr.translation Ψ.1.G Ψ.1.O).π_eq_π_iff).1 h'
  refine ⟨m.1, ?_⟩
  change m.1 • m.2 = x' at ht
  change m.2 = x at hs
  rw [← hs]; exact ht

variable (hT hS) in
/-- **2021 Lemma 17.4.22, p. 804 (closedness)**: `σ` maps closed sets to closed sets. -/
theorem isClosedMap_bdrySigma (hc : S.HatContinuous) (hcent : S.IsCentred) :
    IsClosedMap (S.bdrySigma hT hS) := by
  classical
  intro A hA
  rw [← isOpen_compl_iff]
  refine isOpen_iff_forall_mem_open.2 fun w hw => ?_
  induction w using Quotient.inductionOn with
  | h β =>
    let Ψ := S.bdryRefUnif hS β
    let o := S.refPt hS β
    have ho : Ψ.1.obj o = β := obj_refPt hS β
    have hfix : Ψ.1.FixesPoint o := hcent.fixesPoint (bdryRefUnif_mem hS β) ho
    by_cases hb : o ∈ Ψ.1.P.boundary
    · obtain ⟨V, -⟩ := exists_goodNbhd (S.isTame_unif hT Ψ) hb isOpen_univ (mem_univ _)
      have hnot : ∀ θ : V.faces,
          (S.bdryGroupoid hT hS).π (V.faceObj hT hS θ.2 o (V.mem_of_mem_faces θ.2)) ∈ Aᶜ := by
        intro θ hθA
        refine hw ⟨_, hθA, ?_⟩
        rw [bdrySigma_π, GoodNbhd.faceObj_α, ho]
        rfl
      have hAc : IsBdryOpen hT hS Aᶜ := hA.isOpen_compl
      choose N hN hoN hNA using fun θ : V.faces =>
        hAc.exists_nhds V θ.2 (V.mem_of_mem_faces θ.2) (hnot θ)
      have hfin : Finite V.faces := by
        have h := V.encard_faces
        exact Set.finite_of_encard_eq_coe h
      let N₀ := ⋂ θ : V.faces, N θ
      have hN₀ : IsOpen N₀ := isOpen_iInter_of_finite hN
      let W := V.1.U ∩ ⋂ g : Ψ.1.G, (fun y => g • y) ⁻¹' N₀
      have hW : IsOpen W := V.isOpen.inter (isOpen_iInter_of_finite fun g =>
        hN₀.preimage (EpGroupoid.Examples.action_continuous_smul Ψ.1.smooth_smul g))
      refine ⟨(fun q : Ψ.1.O => C.toGroupoidStr.π (Ψ.1.obj q)) '' W, ?_,
        Ψ.1.isOpenMap_π_obj _ hW, ⟨o, ⟨V.mem, mem_iInter.2 fun g => ?_⟩, congrArg _ ho⟩⟩
      · rintro _ ⟨x, ⟨hxU, hxg⟩, rfl⟩ ⟨z, hzA, hz⟩
        induction z using Quotient.inductionOn with
        | h a =>
          obtain ⟨θ, hθ, x', hx', hπ⟩ := V.exists_mem_faceImage hc hfix
            (z := (S.bdryGroupoid hT hS).π a) ⟨x, hxU, hz.symm⟩
          have hσ := congrArg (S.bdrySigma hT hS) hπ
          rw [bdrySigma_π, GoodNbhd.faceObj_α] at hσ
          have hσ' : C.toGroupoidStr.π (Ψ.1.obj x) = C.toGroupoidStr.π (Ψ.1.obj x') :=
            hz.symm.trans hσ.symm
          obtain ⟨g, hg⟩ := exists_smul_eq_of_π_obj_eq hσ'
          have hx'N : x' ∈ N ⟨θ, hθ⟩ := by
            rw [← hg]; exact mem_iInter.1 (mem_iInter.1 hxg g) ⟨θ, hθ⟩
          exact hNA ⟨θ, hθ⟩ ⟨x', hx', hx'N, hπ⟩ hzA
      · change g • o ∈ N₀
        rw [hfix g]
        exact mem_iInter.2 hoN
    · refine ⟨(fun q : Ψ.1.O => C.toGroupoidStr.π (Ψ.1.obj q)) '' (Ψ.1.P.boundary)ᶜ, ?_,
        Ψ.1.isOpenMap_π_obj _ Ψ.1.P.isClosed_boundary.isOpen_compl, ⟨o, hb, congrArg _ ho⟩⟩
      rintro _ hy ⟨z, -, rfl⟩
      exact (isEmpty_bdrySigma_preimage_compl (hT := hT) (hS := hS) Ψ).false ⟨z, hy⟩

variable (hT hS) in
/-- **2021 Lemma 17.4.22, p. 804**: `σ` is continuous and maps closed sets to closed sets. -/
theorem lemma_17_4_22 (hc : S.HatContinuous) (hcent : S.IsCentred) :
    Continuous (S.bdrySigma hT hS) ∧ IsClosedMap (S.bdrySigma hT hS) :=
  ⟨continuous_bdrySigma, isClosedMap_bdrySigma hT hS hc hcent⟩

/-! ### Definition 17.4.17 as printed -/

section Literal

open MPolyfold TameBoundaryExample

attribute [local instance] quadrantTrivialAction

/-- **2021 Lemma 17.4.18 with "`z ∈ |bC|`" of Definition 17.4.17 taken literally**: with the
condition required at every `z ∈ |bC|`, the empty set would not be open ("Clearly `∅` and `|bC|`
belong to our collection") already for the quadrant polyfold, whose `bC` has objects over the
corner.  We read `z ∈ Q` (`IsBdryOpen`), as the proof does. -/
theorem lemma_17_4_18_literal (W : ScBanach) :
    ∃ (hT : (quadrantConstruction W).IsTame) (hS : (quadrantConstruction W).HasUniformizers),
      ¬ IsBdryOpenLiteral hT hS ∅ := by
  obtain ⟨hT, hS, -, -, h2, -⟩ := quadrant_tameBoundaryUniformizer_witness W
  obtain ⟨a, -⟩ := Set.nonempty_of_encard_ne_zero (s := {a : (quadrantConstruction W).BObj hT hS |
    a.α = quadrantCorner W}) (by rw [h2]; decide)
  exact ⟨hT, hS, not_isBdryOpenLiteral_empty a⟩

end Literal

end GCT.PolyfoldConstruction

end Polyfold
