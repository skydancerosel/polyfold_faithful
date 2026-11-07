import Polyfold.Chapter7.Basic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §7.1:
**Definition 7.10** (ep-subgroupoid, p. 237), the facts (1)–(4) of Proposition 2.6 recalled for
`A` before Proposition 7.7 (pp. 237–238), the construction of the M-polyfold `𝐀` (p. 238) and
**Proposition 7.7** (pp. 238–239).  There is no 2014 preprint of Part II; numbers and pages are
the 2017 text's.  Part I items carry their 2017 numbers, with the preprint number of the Lean name
in brackets: Proposition 2.6 [2.21] (`MPolyfold.subPolyfold`), Definition 2.12 [2.20]
(`MPolyfold.IsSubMPolyfold`), Proposition 2.15 [2.46] (`MPolyfold.isSubMPolyfold_fibredProduct`),
Theorem 2.2 [2.16] (`MPolyfold.paracompactSpace_subtype`).

# Ep-subgroupoids

## The text, paraphrased

(Definition 7.10) An ep-subgroupoid of `X` is the full subcategory on a subset `A` of the object
space which is (1) a sub-M-polyfold of `X` and (2) saturated, `π⁻¹(π(A)) = A`.  (pp. 237–238) By
Proposition 2.6, `A` has an M-polyfold structure with (1) the inclusion `i : A → X` sc-smooth and
a homeomorphism onto its image; (2) `i⁻¹ ∘ r : V → A` sc-smooth for every sc-smooth retraction
`r : V → V` with `r(V) = A ∩ V`; (3) `T_aA` has an sc-complement in `T_aX` at smooth `a`; (4)
`T_aA = Tr(a) T_aX`.  (p. 238) `𝐀 = {φ | s(φ), t(φ) ∈ A}` is a sub-M-polyfold of `𝐗`: for
`φ ∈ 𝐀`, `a = s(φ)`, a sheet `s : 𝐔(φ) → U(a)` and (after shrinking) a retraction
`r : U(a) → U(a)` onto `U(a) ∩ A`, `𝐫 = (s|𝐔(φ))⁻¹ ∘ r ∘ s` is an sc-smooth retraction of `𝐔(φ)`
onto `𝐔(φ) ∩ 𝐀`, by saturation.  `s, t : 𝐀 → A` are local sc-diffeomorphisms, since a sheet maps
`𝐔(φ) ∩ 𝐀` onto `U(a) ∩ A`; `u`, `ι`, `m` are restrictions of sc-smooth maps, hence sc-smooth;
(pp. 238–239) properness holds for `U(a) ∩ A`, `U(a)` a neighbourhood with the natural `G_a`-action
and `t : s⁻¹(cl_X U(a)) → X` proper: for `s(φ_k) ∈ cl_A(U(a) ∩ A)` and `t(φ_k) → c ∈ A`, a
subsequence converges to some `φ` in `𝐗`, and `s(φ) ∈ A` by saturation.  (Proposition 7.7) For a
saturated sub-M-polyfold `A`, the full subcategory on `A` is an ep-groupoid; `A` and `𝐀` are
sub-M-polyfolds of `X` and `𝐗`, and all structure maps are the restrictions of those of `X`.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **Definition 7.10** is `IsEpSubgroupoid` (with `isEpSubgroupoid_univ`), in `EpGroupoid.lean`.
* **The facts (1), (2)**, for `A` and for `𝐀`: `isScSmoothMap_val_subObj`,
  `isScSmoothOn_retractInto_subObj`, `isScSmoothMap_val_subMor`,
  `isScSmoothOn_retractInto_subMor`; the M-polyfolds `subObjPolyfold hA`, `subMorPolyfold hA`.
* **`𝐀`** (p. 238): `morOn_eq_preimage_src`, `morOn_eq_preimage_tgt` (`𝐀 = s⁻¹(A) = t⁻¹(A)` for
  saturated `A`), `src_mem_of_tgt_mem_of_isSaturated`, `isSubMPolyfold_preimage_src`,
  `isSubMPolyfold_preimage_tgt` (the retraction pulled back along `s`, resp. `t`),
  `isSubMPolyfold_morOn`; the scoped instance `instParacompactSpaceMorOn`.
* **The conditions of Definition 7.3** for `fullSub A`: (1) `isLocalScDiffeo_fullSub_src`,
  `isLocalScDiffeo_fullSub_tgt`; (2) `isScSmoothMap_fullSub_unit`, `isScSmoothMap_fullSub_inv`;
  (3) `exists_isProperMap_fullSub`; (4) `isScSmoothComp_fullSub`; `fullSub_comp_val`.
* **Proposition 7.7**: `subEpGroupoid hA : EpGroupoid A (X.morOn A)` and `proposition_7_7` (`A`,
  `𝐀` are sub-M-polyfolds; `toGroupoidStr = fullSub A`, `PObj`, `PMor` the sub-M-polyfold
  structures; `s, t, u, ι, m` the restrictions), with `subEpGroupoid_src_val`, `_tgt_val`,
  `_unit_val`, `_inv_val`, `_comp_val`.  `subEpFunctor hA : EpFunctor (subEpGroupoid hA) X`, the
  inclusion as a morphism of `EP` (Definition 7.7), full and faithful (`subEpFunctor_full`,
  `subEpFunctor_faithful`).
* **Satisfiability**: `isEpSubgroupoid_univ` (`EpGroupoid.lean`), `isEpSubgroupoid_of_isOpen`
  (every saturated open set), `isEpSubgroupoid_saturation` (`π⁻¹(π(U))` for open `U`, by
  Proposition 7.1), `isEpSubgroupoid_trivial` (every sub-M-polyfold of the trivial ep-groupoid).

## Reading

* **Facts (3), (4)** (tangent spaces) are Part I's `proposition_2_21_3`, `proposition_2_21_4`, in
  a chart; they are not restated for `A` or `𝐀`, since `T_xX` carries no linear structure in
  Part I (gap G.7).  Nothing below uses them.
* **Paracompactness** (an M-polyfold is paracompact, Definition 2.8): the text is silent for `A`
  and `𝐀`; both are subspaces of metrizable spaces (Theorem 2.2 [2.16]).  For `𝐀` it is the scoped
  instance `instParacompactSpaceMorOn` (`open scoped Polyfold.EpGroupoid`).  For `A` it is an
  instance argument `[ParacompactSpace A]`, as in Part I's `subPolyfold`: `↥A` does not mention
  `X`, so no instance could find `X.PObj`.  It is always discharged by
  `haveI := X.PObj.paracompactSpace_subtype A`, and it is a `Prop`, so there are no diamonds.
* **`𝐀` is a sub-M-polyfold** in a slightly more general form: the preimage of a sub-M-polyfold
  under a local sc-diffeomorphism is one (saturation is not needed), and saturation gives
  `𝐀 = s⁻¹(A)`.  The text's "possibly smaller `U(a)`" with `r(U(a)) ⊆ U(a)` is
  `U = (V ∩ V₀) ∩ r⁻¹(V ∩ V₀)` (as Part I's `SubData.shrink`), `V = s(𝐔(φ))`.  The extracted text
  reads "`s(𝐫(ψ)) = r(s(ψ)) ∈ A` and `t(𝐫(ψ)) ∈ U(a)`"; as we read it, the second claim does not
  hold in general (`t(𝐫(ψ))` lies near `t(φ)`, not near `a = s(φ)`) and is not needed:
  `s(𝐫(ψ)) ∈ A` and saturation give `t(𝐫(ψ)) ∈ A` (possible misprint for `s(𝐫(ψ)) ∈ U(a)`).
* **Unstated in (1), (2), (4)**: a map into a sub-M-polyfold which is sc-smooth into the ambient
  M-polyfold is sc-smooth into the sub-M-polyfold (near a point it is `(i⁻¹ ∘ r) ∘ i ∘ f`, by fact
  (2)); this is the private `isScSmoothOn_subPolyfold_of_val`.  For `m` (literal condition (4), not
  the sheet form) it is applied twice: the inclusion `𝐀 ₛ×ₜ 𝐀 → 𝐗 ₛ×ₜ 𝐗` is sc-smooth between the
  fibred-product M-polyfolds of Proposition 2.15 [2.46], and `m` of `A` is `m` of `X` composed with
  it.  `fullSub`'s composition of a non-composable pair is a junk value; (4) only concerns
  `𝐀 ₛ×ₜ 𝐀`.
* **(3)**: the text uses a `U(a)` "equipped with the natural `G_a`-action" for which
  `t : s⁻¹(cl_X U(a)) → X` is proper (which tacitly shrinks inside `V(a)`,
  `isProperMap_domRestrict_closure_mono`) and notes that `U(a) ∩ A` is `G_a`-invariant; the
  invariance is not used, and any `V(a)` of Definition 7.3 (3) works: `exists_isProperMap_fullSub`
  takes `V(a) ∩ A`.  "We may assume `φ_k → φ`" is a subsequence (the sequential criterion of
  `ProperMaps.lean`, both spaces metrizable); `cl_A(V ∩ A) ⊆ cl_X V`, and the limit lies over
  `cl_A(V ∩ A)` since this set is closed in `A`.
* **"All structure maps are the restrictions"** is `toGroupoidStr = fullSub A` together with the
  equations `subEpGroupoid_src_val`, …; that the inclusion is a full and faithful morphism of `EP`
  is not stated in the text and is immediate.
* **Hypotheses.**  No hypothesis "for all charts" or "for all retractions" is added: Definition
  2.12 [2.20] asks for *some* retraction at each point, and the facts (2) quantify over all
  retractions only in their conclusions.  `IsEpSubgroupoid A` is satisfiable (the witnesses above,
  e.g. `univ` and the saturations of open sets).
-/

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### Sub-M-polyfolds: maps into them, preimages and restrictions -/

section Helpers

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- **A map into a sub-M-polyfold** `A ⊆ Y` is sc-smooth into `A` as soon as it is sc-smooth into
`Y`: near `x`, `f = (i⁻¹ ∘ r) ∘ i ∘ f` for a retraction `r` onto `A` near `f(x)`, and `i⁻¹ ∘ r` is
sc-smooth (fact (2), Proposition 2.6 (2) [2.21 (2)]). -/
private theorem isScSmoothOn_subPolyfold_of_val {A : Set Y} (hA : Q.IsSubMPolyfold A)
    [ParacompactSpace A] {f : X → A} {U : Set X}
    (hf : P.IsScSmoothOn Q (fun x => (f x : Y)) U) :
    P.IsScSmoothOn (MPolyfold.subPolyfold hA) f U := by
  refine MPolyfold.IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : Y)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (MPolyfold.subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

/-- An sc-smooth map restricted to a sub-M-polyfold `B` of its domain (composed with the
inclusion, fact (1)). -/
private theorem isScSmoothOn_comp_val {B : Set X} (hB : P.IsSubMPolyfold B) [ParacompactSpace B]
    {g : X → Y} {U : Set X} (hg : P.IsScSmoothOn Q g U) :
    (MPolyfold.subPolyfold hB).IsScSmoothOn Q (fun b : B => g b) (Subtype.val ⁻¹' U) :=
  MPolyfold.IsScSmoothOn.comp hg ((MPolyfold.subPolyfold_inclusion_isScSmooth hB).mono
    (hg.isOpen.preimage continuous_subtype_val) (subset_univ _)) fun _ h => h

/-- **The preimage of a sub-M-polyfold under a local sc-diffeomorphism** is a sub-M-polyfold: for
an sc-diffeomorphism `f : W → V` with inverse `g` and a retraction `r` onto `A`, `g ∘ r ∘ f` is a
retraction onto `f⁻¹(A)` near `x` (the text's `𝐫 = (s|𝐔(φ))⁻¹ ∘ r ∘ s`, p. 238). -/
private theorem isSubMPolyfold_preimage_of_isLocalScDiffeo {f : X → Y}
    (hf : P.IsLocalScDiffeo Q f) {A : Set Y} (hA : Q.IsSubMPolyfold A) :
    P.IsSubMPolyfold (f ⁻¹' A) := by
  intro x hx
  obtain ⟨W, V, g, hxW, hd⟩ := hf x
  obtain ⟨V₀, hV₀, hfxV₀, r, -, hrs, hri, hrA⟩ := hA (f x) hx
  have hr_eq : ∀ y ∈ A ∩ V₀, r y = y := fun y hy => by
    rw [← hrA] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hri z hz
  have hr_mem : ∀ y ∈ V₀, r y ∈ A := fun y hy => by
    have h : r y ∈ r '' V₀ := mem_image_of_mem r hy
    rw [hrA] at h
    exact h.1
  have hVo : IsOpen V := hd.isScSmoothOn_inv.isOpen
  -- `U = (V ∩ V₀) ∩ r⁻¹(V ∩ V₀)`, mapped into itself by `r`
  set U := (V ∩ V₀) ∩ r ⁻¹' (V ∩ V₀) with hU
  have hUo : IsOpen U := (hrs.continuousOn.mono inter_subset_right).isOpen_inter_preimage
    (hVo.inter hV₀) (hVo.inter hV₀)
  set W' := W ∩ f ⁻¹' U with hW'
  have hW'o : IsOpen W' :=
    hd.isScSmoothOn.continuousOn.isOpen_inter_preimage hd.isScSmoothOn.isOpen hUo
  have hfx : f x ∈ U := ⟨⟨hd.mapsTo hxW, hfxV₀⟩, by
    rw [mem_preimage, hr_eq _ ⟨hx, hfxV₀⟩]; exact ⟨hd.mapsTo hxW, hfxV₀⟩⟩
  have hrU : ∀ y ∈ W', r (f y) ∈ U := fun y hy =>
    ⟨hy.2.2, by rw [mem_preimage, hri _ hy.2.1.2]; exact hy.2.2⟩
  have hmaps : MapsTo (g ∘ r ∘ f) W' W' := fun y hy => by
    have h1 : r (f y) ∈ V := (hrU y hy).1.1
    refine ⟨hd.mapsTo_inv h1, ?_⟩
    simp only [Function.comp_apply, mem_preimage, hd.right_inv _ h1]
    exact hrU y hy
  refine ⟨W', hW'o, ⟨hxW, hfx⟩, g ∘ r ∘ f, hmaps, ?_, fun y hy => ?_, ?_⟩
  · exact MPolyfold.IsScSmoothOn.comp hd.isScSmoothOn_inv
      (MPolyfold.IsScSmoothOn.comp hrs (hd.isScSmoothOn.mono hW'o inter_subset_left)
        fun y hy => hy.2.1.2) fun y hy => (hrU y hy).1.1
  · simp only [Function.comp_apply, hd.right_inv _ (hrU y hy).1.1, hri _ hy.2.1.2]
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, hmaps hz⟩
      simp only [Function.comp_apply, mem_preimage, hd.right_inv _ (hrU z hz).1.1]
      exact hr_mem _ hz.2.1.2
    · rintro ⟨hyA, hy⟩
      refine ⟨y, hy, ?_⟩
      simp only [Function.comp_apply]
      rw [hr_eq _ ⟨hyA, hy.2.1.2⟩, hd.left_inv _ hy.1]

/-- **A local sc-diffeomorphism restricts** to a local sc-diffeomorphism `B → A` between
sub-M-polyfolds when `B = f⁻¹(A)`: a sheet `f : W → V` maps `W ∩ B` bijectively onto `V ∩ A`
(p. 238). -/
private theorem isLocalScDiffeo_subPolyfold {f : X → Y} (hf : P.IsLocalScDiffeo Q f)
    {A : Set Y} {B : Set X} (hA : Q.IsSubMPolyfold A) (hB : P.IsSubMPolyfold B)
    [ParacompactSpace A] [ParacompactSpace B] (hBA : ∀ x, x ∈ B ↔ f x ∈ A) {f' : B → A}
    (hf' : ∀ b, (f' b : Y) = f b) :
    (MPolyfold.subPolyfold hB).IsLocalScDiffeo (MPolyfold.subPolyfold hA) f' := by
  classical
  intro b
  obtain ⟨W, V, g, hbW, hd⟩ := hf b.1
  have hgB : ∀ a : A, a.1 ∈ V → g a.1 ∈ B := fun a ha =>
    (hBA _).2 (by rw [hd.right_inv _ ha]; exact a.2)
  let g' : A → B := fun a => if h : g a.1 ∈ B then ⟨g a.1, h⟩ else b
  have hg' : ∀ a : A, a.1 ∈ V → (g' a : X) = g a.1 := fun a ha => by
    simp only [g', dif_pos (hgB a ha)]
  have hf'V : ∀ c : B, c.1 ∈ W → (f' c : Y) ∈ V := fun c hc => by
    rw [hf']; exact hd.mapsTo hc
  refine ⟨Subtype.val ⁻¹' W, Subtype.val ⁻¹' V, g', hbW, ?_⟩
  exact
    { isScSmoothOn := isScSmoothOn_subPolyfold_of_val hA
        ((isScSmoothOn_comp_val hB hd.isScSmoothOn).congr fun c _ => (hf' c).symm)
      isScSmoothOn_inv := isScSmoothOn_subPolyfold_of_val hB
        ((isScSmoothOn_comp_val hA hd.isScSmoothOn_inv).congr fun a ha => (hg' a ha).symm)
      mapsTo := fun c hc => hf'V c hc
      mapsTo_inv := fun a ha => by
        change (g' a : X) ∈ W
        rw [hg' a ha]; exact hd.mapsTo_inv ha
      left_inv := fun c hc => Subtype.ext (by rw [hg' _ (hf'V c hc), hf', hd.left_inv _ hc])
      right_inv := fun a ha => Subtype.ext (by rw [hf', hg' a ha, hd.right_inv _ ha]) }

/-- An open subset is a sub-M-polyfold (`V = A`, `r = id`). -/
private theorem isSubMPolyfold_of_isOpen {A : Set X} (hA : IsOpen A) : P.IsSubMPolyfold A :=
  fun a ha => ⟨A, hA, ha, id, mapsTo_id _, MPolyfold.isScSmoothMap_id.mono hA (subset_univ _),
    fun _ _ => rfl, by rw [image_id, inter_self]⟩

end Helpers

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### The morphisms over a saturated set -/

variable {X} in
/-- For a saturated `A`, `t(φ) ∈ A` implies `s(φ) ∈ A` (`isSaturated_iff` applied to `φ⁻¹`). -/
theorem src_mem_of_tgt_mem_of_isSaturated {A : Set Obj} (hA : X.IsSaturated A) {φ : Mor}
    (h : X.tgt φ ∈ A) : X.src φ ∈ A := by
  have h' := X.isSaturated_iff.1 hA (X.inv φ) (by rw [X.src_inv]; exact h)
  rwa [X.tgt_inv] at h'

/-- For a saturated `A`, `𝐀 = s⁻¹(A)` (p. 238). -/
theorem morOn_eq_preimage_src {A : Set Obj} (hA : X.IsSaturated A) :
    X.morOn A = X.src ⁻¹' A :=
  ext fun φ => ⟨fun h => h.1, fun h => ⟨h, X.isSaturated_iff.1 hA φ h⟩⟩

/-- For a saturated `A`, `𝐀 = t⁻¹(A)`. -/
theorem morOn_eq_preimage_tgt {A : Set Obj} (hA : X.IsSaturated A) :
    X.morOn A = X.tgt ⁻¹' A :=
  ext fun _ => ⟨fun h => h.2, fun h => ⟨src_mem_of_tgt_mem_of_isSaturated hA h, h⟩⟩

/-- **The pull-back of a sub-M-polyfold along `s`**: `s⁻¹(A)` is a sub-M-polyfold of `𝐗` (the
retraction `(s|𝐔(φ))⁻¹ ∘ r ∘ s` of p. 238). -/
theorem isSubMPolyfold_preimage_src {A : Set Obj} (hA : X.PObj.IsSubMPolyfold A) :
    X.PMor.IsSubMPolyfold (X.src ⁻¹' A) :=
  isSubMPolyfold_preimage_of_isLocalScDiffeo X.isLocalScDiffeo_src hA

/-- `t⁻¹(A)` is a sub-M-polyfold of `𝐗`. -/
theorem isSubMPolyfold_preimage_tgt {A : Set Obj} (hA : X.PObj.IsSubMPolyfold A) :
    X.PMor.IsSubMPolyfold (X.tgt ⁻¹' A) :=
  isSubMPolyfold_preimage_of_isLocalScDiffeo X.isLocalScDiffeo_tgt hA

/-- **`𝐀 = {φ | s(φ), t(φ) ∈ A}` is a sub-M-polyfold of `𝐗`** (Proposition 7.7, pp. 238–239). -/
theorem isSubMPolyfold_morOn {A : Set Obj} (hA : X.IsEpSubgroupoid A) :
    X.PMor.IsSubMPolyfold (X.morOn A) := by
  rw [X.morOn_eq_preimage_src hA.isSaturated]
  exact X.isSubMPolyfold_preimage_src hA.isSubMPolyfold

/-- The morphism set `𝐀` of the full subcategory on `A` is paracompact (a subspace of the
metrizable `𝐗`, Theorem 2.2 [2.16]).  Scoped: `open scoped Polyfold.EpGroupoid`. -/
scoped instance instParacompactSpaceMorOn (A : Set Obj) : ParacompactSpace (X.morOn A) :=
  X.PMor.paracompactSpace_subtype _

/-- The composition of the full subcategory is that of `X` on composable pairs. -/
theorem fullSub_comp_val {A : Set Obj} (φ ψ : X.morOn A) (h : X.src φ.1 = X.tgt ψ.1) :
    ((X.fullSub A).comp φ ψ : Mor) = X.comp φ ψ := by
  simp only [GroupoidStr.fullSub, dif_pos h]

/-! ### Proposition 7.7 -/

section Sub

variable {X} {A : Set Obj} (hA : X.IsEpSubgroupoid A)

/-- The M-polyfold structure of `𝐀 = morOn A`. -/
abbrev subMorPolyfold : MPolyfold (X.morOn A) := MPolyfold.subPolyfold (X.isSubMPolyfold_morOn hA)

/-! #### The facts (1)–(2) of Proposition 2.6 [2.21], for `𝐀` and `A` (pp. 237–238) -/

/-- **Fact (1) for `𝐀`**: the inclusion `𝐀 → 𝐗` is sc-smooth and a homeomorphism onto its
image. -/
theorem isScSmoothMap_val_subMor :
    (subMorPolyfold hA).IsScSmoothMap X.PMor Subtype.val ∧
      IsEmbedding (Subtype.val : X.morOn A → Mor) :=
  ⟨MPolyfold.subPolyfold_inclusion_isScSmooth _, IsEmbedding.subtypeVal⟩

/-- **Fact (2) for `𝐀`**: for every sc-smooth retraction `r : V → V` of an open `V ⊆ 𝐗` with
`r(V) = 𝐀 ∩ V`, `i⁻¹ ∘ r : V → 𝐀` is sc-smooth. -/
theorem isScSmoothOn_retractInto_subMor (d : X.PMor.SubData (X.morOn A)) (a₀ : X.morOn A) :
    X.PMor.IsScSmoothOn (subMorPolyfold hA) (d.retractInto a₀) d.V :=
  MPolyfold.subPolyfold_retraction_isScSmooth _ d a₀

/-- **(2)**: the inversion of the full subcategory on `A` is sc-smooth. -/
theorem isScSmoothMap_fullSub_inv :
    (subMorPolyfold hA).IsScSmoothMap (subMorPolyfold hA) (X.fullSub A).inv :=
  isScSmoothOn_subPolyfold_of_val _
    (X.isScSmoothMap_inv.comp (MPolyfold.subPolyfold_inclusion_isScSmooth _))

variable [ParacompactSpace A]

/-- The M-polyfold structure of `A` (Proposition 2.6 [2.21]). -/
abbrev subObjPolyfold : MPolyfold A := MPolyfold.subPolyfold hA.isSubMPolyfold

/-- **Fact (1) for `A`**: the inclusion `i : A → X` is sc-smooth and a homeomorphism onto its
image. -/
theorem isScSmoothMap_val_subObj :
    (subObjPolyfold hA).IsScSmoothMap X.PObj Subtype.val ∧ IsEmbedding (Subtype.val : A → Obj) :=
  ⟨MPolyfold.subPolyfold_inclusion_isScSmooth _, IsEmbedding.subtypeVal⟩

/-- **Fact (2) for `A`**: for every sc-smooth retraction `r : V → V` of an open `V ⊆ X` with
`r(V) = A ∩ V`, `i⁻¹ ∘ r : V → A` is sc-smooth. -/
theorem isScSmoothOn_retractInto_subObj (d : X.PObj.SubData A) (a₀ : A) :
    X.PObj.IsScSmoothOn (subObjPolyfold hA) (d.retractInto a₀) d.V :=
  MPolyfold.subPolyfold_retraction_isScSmooth _ d a₀

/-! #### The conditions of Definition 7.3 for the full subcategory -/

/-- **(1)**: `s : 𝐀 → A` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_fullSub_src :
    (subMorPolyfold hA).IsLocalScDiffeo (subObjPolyfold hA) (X.fullSub A).src :=
  isLocalScDiffeo_subPolyfold X.isLocalScDiffeo_src hA.isSubMPolyfold (X.isSubMPolyfold_morOn hA)
    (fun φ => ⟨fun h => h.1, fun h => ⟨h, X.isSaturated_iff.1 hA.isSaturated φ h⟩⟩) fun _ => rfl

/-- **(1)**: `t : 𝐀 → A` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_fullSub_tgt :
    (subMorPolyfold hA).IsLocalScDiffeo (subObjPolyfold hA) (X.fullSub A).tgt :=
  isLocalScDiffeo_subPolyfold X.isLocalScDiffeo_tgt hA.isSubMPolyfold (X.isSubMPolyfold_morOn hA)
    (fun _ => ⟨fun h => h.2, fun h => ⟨src_mem_of_tgt_mem_of_isSaturated hA.isSaturated h, h⟩⟩)
    fun _ => rfl

/-- **(2)**: the unit map of `A` is sc-smooth. -/
theorem isScSmoothMap_fullSub_unit :
    (subObjPolyfold hA).IsScSmoothMap (subMorPolyfold hA) (X.fullSub A).unit :=
  isScSmoothOn_subPolyfold_of_val _
    (X.isScSmoothMap_unit.comp (MPolyfold.subPolyfold_inclusion_isScSmooth _))

include hA in
/-- **(3)**: properness restricts.  For `a ∈ A` and `V = V(a)` of Definition 7.3 (3) for `X`,
the open `V ∩ A` has the property for `A` (the argument of p. 239). -/
theorem exists_isProperMap_fullSub (a : A) : ∃ V : Set A, IsOpen V ∧ a ∈ V ∧
    IsProperMap (((X.fullSub A).src ⁻¹' closure V).domRestrict (X.fullSub A).tgt) := by
  obtain ⟨V, hVo, haV, hV⟩ := X.exists_isProperMap a.1
  refine ⟨Subtype.val ⁻¹' V, hVo.preimage continuous_subtype_val, haV, ?_⟩
  rw [MPolyfold.isProperMap_domRestrict_iff_of_isClosed (subMorPolyfold hA) (subObjPolyfold hA)
    (isLocalScDiffeo_fullSub_src hA).continuous (isLocalScDiffeo_fullSub_tgt hA).continuous
    isClosed_closure]
  intro φ y hφ hy
  have hφ' : ∀ n, X.src (φ n : Mor) ∈ closure V := fun n =>
    continuous_subtype_val.closure_preimage_subset V (hφ n)
  have hy' : Tendsto (X.tgt ∘ fun n => (φ n : Mor)) atTop (𝓝 (y : Obj)) :=
    (continuous_subtype_val.tendsto y).comp hy
  obtain ⟨φ₀, -, hφ₀t, ψ, hψ, hlim⟩ :=
    MPolyfold.exists_tendsto_subseq_of_isProperMap_domRestrict X.PMor hV hφ' hy'
  have hφ₀A : X.tgt φ₀ ∈ A := by rw [hφ₀t]; exact y.2
  exact ⟨⟨φ₀, src_mem_of_tgt_mem_of_isSaturated hA.isSaturated hφ₀A, hφ₀A⟩, ψ, hψ,
    tendsto_subtype_rng.2 hlim⟩

/-- **(4)**: the multiplication of `A` is sc-smooth on `𝐀 ₛ×ₜ 𝐀`: it is the multiplication of
`X` composed with the inclusion `j : 𝐀 ₛ×ₜ 𝐀 → 𝐗 ₛ×ₜ 𝐗`. -/
theorem isScSmoothComp_fullSub :
    IsScSmoothComp (subObjPolyfold hA) (subMorPolyfold hA) (X.fullSub A).src (X.fullSub A).tgt
      (X.fullSub A).comp (isLocalScDiffeo_fullSub_src hA)
      (isLocalScDiffeo_fullSub_tgt hA).isScSmoothMap := by
  let PM := subMorPolyfold hA
  let _ := MPolyfold.paracompactSpace_prod PM PM
  let _ := (PM.prod PM).paracompactSpace_subtype
    (MPolyfold.fibredProduct (X.fullSub A).src (X.fullSub A).tgt)
  let _ := MPolyfold.paracompactSpace_prod X.PMor X.PMor
  let _ := (X.PMor.prod X.PMor).paracompactSpace_subtype (MPolyfold.fibredProduct X.src X.tgt)
  have hF := MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src X.isScSmoothMap_tgt
  have hF' := MPolyfold.isSubMPolyfold_fibredProduct (isLocalScDiffeo_fullSub_src hA)
    (isLocalScDiffeo_fullSub_tgt hA).isScSmoothMap
  have hm : (MPolyfold.subPolyfold hF).IsScSmoothMap X.PMor fun p => X.comp p.1.1 p.1.2 :=
    X.isScSmoothComp
  let j : MPolyfold.fibredProduct (X.fullSub A).src (X.fullSub A).tgt →
      MPolyfold.fibredProduct X.src X.tgt := fun p =>
    ⟨((p.1.1 : Mor), (p.1.2 : Mor)), congrArg Subtype.val p.2⟩
  have hi := MPolyfold.subPolyfold_inclusion_isScSmooth hF'
  have hiM := MPolyfold.subPolyfold_inclusion_isScSmooth (X.isSubMPolyfold_morOn hA)
  have h1 : (MPolyfold.subPolyfold hF').IsScSmoothMap X.PMor fun p => (p.1.1 : Mor) :=
    hiM.comp ((MPolyfold.isScSmoothMap_fst PM PM).comp hi)
  have h2 : (MPolyfold.subPolyfold hF').IsScSmoothMap X.PMor fun p => (p.1.2 : Mor) :=
    hiM.comp ((MPolyfold.isScSmoothMap_snd PM PM).comp hi)
  have hj : (MPolyfold.subPolyfold hF').IsScSmoothMap (MPolyfold.subPolyfold hF) j :=
    isScSmoothOn_subPolyfold_of_val hF (MPolyfold.IsScSmoothOn.prodMk h1 h2)
  change (MPolyfold.subPolyfold hF').IsScSmoothMap PM _
  refine isScSmoothOn_subPolyfold_of_val _ ((hm.comp hj).congr fun p _ => ?_)
  exact (X.fullSub_comp_val p.1.1 p.1.2 (congrArg Subtype.val p.2)).symm

/-- **Proposition 7.7, the structure**: the full subcategory on an ep-subgroupoid `A` is an
ep-groupoid, with the M-polyfold structures of the sub-M-polyfolds `A ⊆ X` and `𝐀 ⊆ 𝐗` and the
restricted structure maps. -/
def subEpGroupoid : EpGroupoid A (X.morOn A) where
  toGroupoidStr := X.fullSub A
  PObj := subObjPolyfold hA
  PMor := subMorPolyfold hA
  isLocalScDiffeo_src := isLocalScDiffeo_fullSub_src hA
  isLocalScDiffeo_tgt := isLocalScDiffeo_fullSub_tgt hA
  isScSmoothMap_unit := isScSmoothMap_fullSub_unit hA
  isScSmoothMap_inv := isScSmoothMap_fullSub_inv hA
  exists_isProperMap := exists_isProperMap_fullSub hA
  isScSmoothComp := isScSmoothComp_fullSub hA

@[simp]
theorem subEpGroupoid_src_val (φ : X.morOn A) : ((subEpGroupoid hA).src φ : Obj) = X.src φ :=
  rfl

@[simp]
theorem subEpGroupoid_tgt_val (φ : X.morOn A) : ((subEpGroupoid hA).tgt φ : Obj) = X.tgt φ :=
  rfl

@[simp]
theorem subEpGroupoid_unit_val (x : A) : ((subEpGroupoid hA).unit x : Mor) = X.unit x :=
  rfl

@[simp]
theorem subEpGroupoid_inv_val (φ : X.morOn A) : ((subEpGroupoid hA).inv φ : Mor) = X.inv φ :=
  rfl

theorem subEpGroupoid_comp_val {φ ψ : X.morOn A}
    (h : (subEpGroupoid hA).src φ = (subEpGroupoid hA).tgt ψ) :
    ((subEpGroupoid hA).comp φ ψ : Mor) = X.comp φ ψ :=
  X.fullSub_comp_val φ ψ (congrArg Subtype.val h)

/-- **Proposition 7.7**: for a saturated sub-M-polyfold `A` of the object space, `A` and
`𝐀 = {φ | s(φ), t(φ) ∈ A}` are sub-M-polyfolds of `X` and `𝐗`, and the full subcategory on `A`
is an ep-groupoid (`subEpGroupoid`) with these M-polyfold structures whose structure maps are the
restrictions of those of `X`. -/
theorem proposition_7_7 :
    X.PObj.IsSubMPolyfold A ∧ X.PMor.IsSubMPolyfold (X.morOn A) ∧
      (subEpGroupoid hA).toGroupoidStr = X.fullSub A ∧
      (subEpGroupoid hA).PObj = MPolyfold.subPolyfold hA.isSubMPolyfold ∧
      (subEpGroupoid hA).PMor = MPolyfold.subPolyfold (X.isSubMPolyfold_morOn hA) ∧
      (∀ φ, ((subEpGroupoid hA).src φ : Obj) = X.src φ) ∧
      (∀ φ, ((subEpGroupoid hA).tgt φ : Obj) = X.tgt φ) ∧
      (∀ x, ((subEpGroupoid hA).unit x : Mor) = X.unit x) ∧
      (∀ φ, ((subEpGroupoid hA).inv φ : Mor) = X.inv φ) ∧
      ∀ φ ψ, (subEpGroupoid hA).src φ = (subEpGroupoid hA).tgt ψ →
        ((subEpGroupoid hA).comp φ ψ : Mor) = X.comp φ ψ :=
  ⟨hA.isSubMPolyfold, X.isSubMPolyfold_morOn hA, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ _ h => subEpGroupoid_comp_val hA h⟩

/-- **The inclusion of an ep-subgroupoid is a morphism of `EP`** (Definition 7.7): the inclusions
`A → X` and `𝐀 → 𝐗`, sc-smooth by fact (1). -/
def subEpFunctor : EpFunctor (subEpGroupoid hA) X where
  obj := Subtype.val
  mor := Subtype.val
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ h := subEpGroupoid_comp_val hA h
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.subPolyfold_inclusion_isScSmooth _
  isScSmoothMap_mor := MPolyfold.subPolyfold_inclusion_isScSmooth _

@[simp]
theorem subEpFunctor_obj (x : A) : (subEpFunctor hA).obj x = x := rfl

@[simp]
theorem subEpFunctor_mor (φ : X.morOn A) : (subEpFunctor hA).mor φ = φ := rfl

/-- **The inclusion is full** (`A` is a *full* subcategory): every morphism `x → y` of `X` between
points of `A` lies in `𝐀`. -/
instance subEpFunctor_full : (subEpFunctor hA).toFunctor.Full where
  map_surjective {x y} f := by
    let x' : A := x
    let y' : A := y
    have hx : X.src f.1 = x'.1 := f.2.1
    have hy : X.tgt f.1 = y'.1 := f.2.2
    exact ⟨⟨⟨f.1, by rw [hx]; exact x'.2, by rw [hy]; exact y'.2⟩, Subtype.ext hx,
      Subtype.ext hy⟩, Subtype.ext rfl⟩

/-- **The inclusion is faithful.** -/
instance subEpFunctor_faithful : (subEpFunctor hA).toFunctor.Faithful where
  map_injective {_ _} {f f'} he := by
    have h := congrArg Subtype.val he
    exact Subtype.ext (Subtype.ext h)

end Sub

/-! ### Satisfiability -/

/-- The saturation of a set is saturated. -/
private theorem isSaturated_saturation' (U : Set Obj) : X.IsSaturated (X.saturation U) := by
  change X.π ⁻¹' (X.π '' (X.π ⁻¹' (X.π '' U))) = X.π ⁻¹' (X.π '' U)
  rw [image_preimage_eq _ X.surjective_π]

/-- **Every saturated open set is an ep-subgroupoid** (an open set is a sub-M-polyfold with
`r = id`). -/
theorem isEpSubgroupoid_of_isOpen {A : Set Obj} (hA : IsOpen A) (hs : X.IsSaturated A) :
    X.IsEpSubgroupoid A :=
  ⟨isSubMPolyfold_of_isOpen hA, hs⟩

/-- **The saturation `π⁻¹(π(U))` of an open `U` is an ep-subgroupoid**: it is open by Proposition
7.1. -/
theorem isEpSubgroupoid_saturation {U : Set Obj} (hU : IsOpen U) :
    X.IsEpSubgroupoid (X.saturation U) :=
  X.isEpSubgroupoid_of_isOpen ((X.proposition_7_1 U hU).preimage X.continuous_π)
    (X.isSaturated_saturation' U)

/-- In the trivial ep-groupoid of an M-polyfold every sub-M-polyfold is an ep-subgroupoid. -/
theorem isEpSubgroupoid_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] (P : MPolyfold Z) {A : Set Z} (hA : P.IsSubMPolyfold A) :
    (trivial P).IsEpSubgroupoid A :=
  ⟨hA, GroupoidStr.isSaturated_trivial A⟩

end EpGroupoid

end Polyfold
