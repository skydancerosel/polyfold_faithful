import Polyfold.Chapter13.GoodSystem
import Polyfold.Chapter7.OrbitTopology
import Polyfold.Chapter7.ProperSubsets

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14:
**Lemma 14.3.6** (p. 654), **Lemma 14.3.7** (p. 655) and **Lemma 14.5.1** (p. 671)
(2017 text: Lemma 14.4, Lemma 14.5, Lemma 14.10).

# Locally finite covers of the boundary and an adapted partition of unity

## The text, paraphrased

(Lemma 14.3.6) For an ep-groupoid with paracompact `|X|` and open neighbourhoods `Ũ(x)`,
`x ∈ ∂X`, with the natural `G_x`-action, there are `A ⊆ ∂X` and nonempty open `Ṽ_a ⊆ Ũ(a)` with
(1) `cl_{|X|}(|Ṽ_a|) ⊆ |Ũ(a)|`, (2) `Ṽ_a` invariant under the natural `G_a`-action, (3) `(|Ṽ_a|)`
a locally finite covering of `|∂X|` by sets open in `|X|`.  (Proof) Refine the cover
`(|Ũ(x)|)_{x ∈ ∂X} ∪ {|X \ ∂X|}` of `|X|` to a locally finite one `(W_a)` with closures inside, and
put `Ṽ_a = Ũ(a) ∩ π⁻¹(W_a)`.
(Lemma 14.3.7) For `a ∈ A` and `y ∈ U'(a) = Ũ'(a) ∩ ∂X` there are a finite `o(y) ⊆ A` and a
`G_y`-invariant open `Õ(y) ∋ y` in `Ũ'(a)` with (1) `|Õ(y)|` meets `|Ṽ_b|` only if `b ∈ o(y)`,
(2) `g ∗ Õ(y) = Õ(g ∗ y)` and `o(g ∗ y) = o(y)` for `g ∈ G_a`, (3) every `φ` with
`s(φ) ∈ Õ(y) ∩ Ũ(a)` and `t(φ) ∈ Ũ(b)`, `b ∈ o(y)`, lies in `Ô_{a,b}`.  (Proof of (3)) By
properness of `cl_X Ũ(b)`: a limit `φ₀` of bad morphisms has `s(φ₀) = y`, `t(φ₀) ∈ cl_X Ũ(b) ∩ ∂X
⊆ U'(b)`, so `φ₀ ∈ U'(a, b) ⊆ Ô_{a,b}`, which is open.
(Lemma 14.5.1) If `X` admits sc-smooth partitions of unity, there are sc-smooth functors
`β_a : X → [0, 1]`, `a ∈ A`, with (1) support in `π⁻¹(π(V̂_a))`, (2) local finiteness on saturated
neighbourhoods, (3) `∑_a β_a = 1` on `∂X`.  (Proof) Take a partition of unity subordinate to the
saturated cover `(π⁻¹(|V̂_a|))_a ∪ {X \ ∂X}` and keep the `β_a`.

## What is formalized (namespace `Polyfold.EpGroupoid`)

The three lemmas are stated in an abstract setting that the Chapter 14 objects instantiate: the
boundary `∂X` is any set `B` of objects (closed in `|X|`, resp. closed and saturated), the
neighbourhoods `Ũ(x)` are `NatNbhd`s (§13.1), `Ũ'(a)` is a `NatNbhd` at `a`, `Ô_{a,b}` any open sets
of morphisms containing `U'(a, b)`, and the cover `(Ṽ_b)` any family with `(|Ṽ_b|)` locally finite.

* `isClosed_π_image_of_isSaturated`: a closed saturated `B` (such as `∂X`) has `|B|` closed.
* **Lemma 14.3.6**: `lemma_14_3_6`.
* `exists_nhds_of_isProperSubset`: the properness step of the proof of Lemma 14.3.7 (3).
* **Lemma 14.3.7**: `lemma_14_3_7` (with (3) for all `φ` with `s(φ) ∈ Õ(y)`, not only those with
  `s(φ) ∈ Õ(y) ∩ Ũ(a)`), `lemma_14_3_7_stab` (the `G_y`-invariance, read as invariance under the
  elements of `G_a` fixing `y`).
* **Lemma 14.5.1**: `lemma_14_5_1`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Closed saturated sets -/

/-- A closed saturated set of objects (such as `∂X`) has closed image in `|X|`. -/
theorem isClosed_π_image_of_isSaturated {B : Set Obj} (hsat : X.IsSaturated B)
    (hB : IsClosed B) : IsClosed (X.π '' B) := by
  have hc : (X.π '' B)ᶜ = X.π '' Bᶜ := by
    ext p
    obtain ⟨y, rfl⟩ := X.surjective_π p
    constructor
    · intro h
      exact ⟨y, fun hy => h ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨y', hy', hyy'⟩ ⟨y'', hy'', h''⟩
      apply hy'
      have hmem : y' ∈ X.π ⁻¹' (X.π '' B) := ⟨y'', hy'', h''.trans hyy'.symm⟩
      rwa [hsat] at hmem
  rw [← isOpen_compl_iff, hc]
  exact X.proposition_7_1_8 _ hB.isOpen_compl

/-- The complement of a saturated set is saturated. -/
theorem isSaturated_compl {B : Set Obj} (hsat : X.IsSaturated B) : X.IsSaturated Bᶜ := by
  refine (X.isSaturated_iff).2 fun φ hφ ht => hφ ?_
  have h := (X.isSaturated_iff).1 hsat (X.inv φ) (by rw [X.src_inv]; exact ht)
  rwa [X.tgt_inv] at h

/-- A saturated set contains the target of every morphism with source in it. -/
theorem IsSaturated.tgt_mem {B : Set Obj} (hsat : X.IsSaturated B) {φ : Mor}
    (h : X.src φ ∈ B) : X.tgt φ ∈ B :=
  (X.isSaturated_iff).1 hsat φ h

/-- `π⁻¹(S)` is saturated. -/
theorem isSaturated_preimage_π (S : Set X.OrbitSpace) : X.IsSaturated (X.π ⁻¹' S) := by
  change X.π ⁻¹' (X.π '' (X.π ⁻¹' S)) = X.π ⁻¹' S
  rw [image_preimage_eq S X.surjective_π]

/-- The saturation of an open set is open. -/
theorem isOpen_saturation {V : Set Obj} (hV : IsOpen V) : IsOpen (X.saturation V) :=
  (X.proposition_7_1_8 V hV).preimage X.continuous_π

/-! ### Lemma 14.3.6 -/

/-- **Lemma 14.3.6, p. 654 (2017: Lemma 14.4)** (locally finite cover of the boundary): let `|X|`
be paracompact,
`B ⊆ X` a set of objects with `|B|` closed in `|X|` (for `B = ∂X`:
`isClosed_π_image_of_isSaturated`), and `N x` an open neighbourhood `Ũ(x)` with the natural
`G_x`-action for every `x`.  Then there are `A ⊆ B` and nonempty open `Ṽ_a ⊆ Ũ(a)`, `a ∈ A`,
with (1) `cl_{|X|}(|Ṽ_a|) ⊆ |Ũ(a)|`, (2) `Ṽ_a`
invariant under the natural `G_a`-action, (3) `(|Ṽ_a|)_{a ∈ A}` a locally finite family of open sets
of `|X|` covering `|B|`. -/
theorem lemma_14_3_6 (hpara : X.HasParacompactOrbitSpace) {B : Set Obj}
    (hB : IsClosed (X.π '' B)) (N : ∀ x : Obj, X.NatNbhd x) :
    ∃ (A : Set Obj) (V : Obj → Set Obj), A ⊆ B ∧
      (∀ a ∈ A, (V a).Nonempty ∧ IsOpen (V a) ∧ V a ⊆ (N a).U ∧
        IsOpen (X.π '' V a) ∧ closure (X.π '' V a) ⊆ X.π '' (N a).U ∧
        ∀ g, MapsTo ((N a).rep.Φ g) (V a) (V a)) ∧
      LocallyFinite (fun a : A => X.π '' V a) ∧ X.π '' B ⊆ ⋃ a ∈ A, X.π '' V a := by
  have : ParacompactSpace X.OrbitSpace := hpara
  let u : Option B → Set X.OrbitSpace := fun o => o.elim (X.π '' B)ᶜ fun x => X.π '' (N x).U
  have uo : ∀ o, IsOpen (u o) := by
    rintro (_ | x)
    · exact hB.isOpen_compl
    · exact X.proposition_7_1_8 _ (N x).isOpen_U
  have uc : ⋃ o, u o = univ := by
    refine eq_univ_of_forall fun p => ?_
    by_cases hp : p ∈ X.π '' B
    · obtain ⟨x, hx, rfl⟩ := hp
      exact mem_iUnion.2 ⟨some ⟨x, hx⟩, ⟨x, (N x).mem_U, rfl⟩⟩
    · exact mem_iUnion.2 ⟨none, hp⟩
  obtain ⟨v, vo, vc, vlf, vsub⟩ := precise_refinement u uo uc
  obtain ⟨w, wc, wo, wcl⟩ := exists_iUnion_eq_closure_subset vo (fun p => vlf.point_finite p) vc
  have wsub : ∀ i, closure (w i) ⊆ u i := fun i => (wcl i).trans (vsub i)
  have wlf : LocallyFinite w := vlf.subset fun i => subset_closure.trans (wcl i)
  classical
  let A : Set Obj := {a | ∃ h : a ∈ B, (w (some ⟨a, h⟩)).Nonempty}
  let V : Obj → Set Obj := fun a =>
    if h : a ∈ B then (N a).U ∩ X.π ⁻¹' w (some ⟨a, h⟩) else ∅
  have hV : ∀ a (h : a ∈ B), V a = (N a).U ∩ X.π ⁻¹' w (some ⟨a, h⟩) := fun a h => dif_pos h
  have himg : ∀ a (h : a ∈ B), X.π '' V a = w (some ⟨a, h⟩) := fun a h => by
    rw [hV a h, image_inter_preimage]
    exact inter_eq_right.2 (subset_closure.trans (wsub (some ⟨a, h⟩)))
  refine ⟨A, V, fun a ha => ha.1, fun a ha => ?_, ?_, ?_⟩
  · obtain ⟨hB', hne⟩ := ha
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← image_nonempty, himg a hB']
      exact hne
    · rw [hV a hB']
      exact (N a).isOpen_U.inter ((wo _).preimage X.continuous_π)
    · rw [hV a hB']
      exact inter_subset_left
    · rw [himg a hB']
      exact wo _
    · rw [himg a hB']
      exact wsub (some ⟨a, hB'⟩)
    · intro g z hz
      rw [hV a hB'] at hz ⊢
      refine ⟨(N a).Φ_mem g hz.1, ?_⟩
      rw [mem_preimage, (N a).π_Φ g ((N a).U_subset hz.1)]
      exact hz.2
  · have heq : (fun a : A => X.π '' V a) =
        w ∘ fun a : A => some (⟨a.1, a.2.1⟩ : B) := by
      funext a
      exact himg a.1 a.2.1
    rw [heq]
    refine wlf.comp_injective fun a b hab => ?_
    have h1 := Option.some_injective _ hab
    have h2 : (a : Obj) = b := congrArg (fun c : B => (c : Obj)) h1
    exact Subtype.ext h2
  · rintro p ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 (wc.symm ▸ mem_univ (X.π x) : X.π x ∈ ⋃ i, w i)
    cases i with
    | none => exact absurd ⟨x, hx, rfl⟩ (subset_closure.trans (wsub none) hi)
    | some a =>
      obtain ⟨a, ha⟩ := a
      refine mem_iUnion₂.2 ⟨a, ⟨ha, X.π x, hi⟩, ?_⟩
      rw [himg a ha]
      exact hi

/-! ### Lemma 14.3.7 -/

/-- **The properness step of Lemma 14.3.7 (3)**: if `Q` is a proper set of objects and every
morphism `φ` with `s(φ) = y` and `t(φ) ∈ Q` lies in the open set `S`, then the same holds for all
`φ` with `s(φ)` in a neighbourhood of `y`. -/
theorem exists_nhds_of_isProperSubset {Q : Set Obj} (hQ : X.IsProperSubset Q) {S : Set Mor}
    (hS : IsOpen S) {y : Obj} (hy : ∀ φ, X.src φ = y → X.tgt φ ∈ Q → φ ∈ S) :
    ∃ W : Set Obj, IsOpen W ∧ y ∈ W ∧ ∀ φ, X.src φ ∈ W → X.tgt φ ∈ Q → φ ∈ S := by
  let f := (X.src ⁻¹' Q).domRestrict X.tgt
  let T : Set (X.src ⁻¹' Q) := {ψ | X.inv ψ.1 ∉ S}
  have hT : IsClosed T :=
    hS.isClosed_compl.preimage (X.continuous_inv.comp continuous_subtype_val)
  have hK : IsClosed (f '' T) := hQ.isClosedMap T hT
  refine ⟨(f '' T)ᶜ, hK.isOpen_compl, ?_, ?_⟩
  · rintro ⟨ψ, hψT, hψy⟩
    apply hψT
    refine hy _ ?_ ?_
    · rw [X.src_inv]
      exact hψy
    · rw [X.tgt_inv]
      exact ψ.2
  · intro φ hφW hφQ
    by_contra hφS
    have hmem : X.inv φ ∈ X.src ⁻¹' Q := by
      rw [mem_preimage, X.src_inv]
      exact hφQ
    apply hφW
    refine ⟨⟨X.inv φ, hmem⟩, ?_, ?_⟩
    · change X.inv (X.inv φ) ∉ S
      rw [GroupoidStr.inv_inv]
      exact hφS
    · change X.tgt (X.inv φ) = X.src φ
      exact X.tgt_inv φ

/-- **Lemma 14.3.7, p. 655 (2017: Lemma 14.5)**: fix `a ∈ A`; `B` (for `∂X`) is saturated, `N'` is
`Ũ'(a)` with the
natural `G_a`-action, `cl_X(Ũ(b)) ⊆ Ũ'(b)` is proper for `b ∈ A`, the open sets `Ô_{a,b}` contain
`U'(a, b) = {φ | s(φ) ∈ Ũ'(a) ∩ B, t(φ) ∈ Ũ'(b) ∩ B}`, and `(|Ṽ_b|)_{b ∈ A}` is locally finite.
Then for every `y ∈ U'(a) = Ũ'(a) ∩ B` there are a finite `o(y) ⊆ A` and an open `Õ(y) ∋ y` inside
`Ũ'(a)` with (1) `|Õ(y)| ∩ |Ṽ_b| ≠ ∅` only for `b ∈ o(y)`, (2) `g ∗ Õ(y) = Õ(g ∗ y)` and
`o(g ∗ y) = o(y)` for `g ∈ G_a`, (3) every `φ` with `s(φ) ∈ Õ(y)` and `t(φ) ∈ Ũ(b)`, `b ∈ o(y)`,
lies in `Ô_{a,b}` (the text asks this for `s(φ) ∈ Õ(y) ∩ Ũ(a)`). -/
theorem lemma_14_3_7 {A B : Set Obj} (hB : X.IsSaturated B) {a : Obj} (N' : X.NatNbhd a)
    {Ut Ut' V : Obj → Set Obj} {O : Obj → Obj → Set Mor}
    (hcl : ∀ b ∈ A, closure (Ut b) ⊆ Ut' b) (hprop : ∀ b ∈ A, X.IsProperSubset (closure (Ut b)))
    (hOo : ∀ b ∈ A, IsOpen (O a b))
    (hO : ∀ b ∈ A, ∀ φ, X.src φ ∈ N'.U ∩ B → X.tgt φ ∈ Ut' b ∩ B → φ ∈ O a b)
    (hlf : LocallyFinite fun b : A => X.π '' V b) :
    ∃ (o : Obj → Set Obj) (Oy : Obj → Set Obj), ∀ y ∈ N'.U ∩ B,
      IsOpen (Oy y) ∧ y ∈ Oy y ∧ Oy y ⊆ N'.U ∧ (o y).Finite ∧ o y ⊆ A ∧
      (∀ b ∈ A, (X.π '' Oy y ∩ X.π '' V b).Nonempty → b ∈ o y) ∧
      (∀ g, N'.rep.Φ g '' Oy y = Oy (N'.rep.Φ g y) ∧ o (N'.rep.Φ g y) = o y) ∧
      (∀ b ∈ o y, ∀ φ, X.src φ ∈ Oy y → X.tgt φ ∈ Ut b → φ ∈ O a b) := by
  classical
  have hfinI : Finite (X.Isotropy a) := X.proposition_7_1_12 a
  -- the domain `U'(a)` is invariant
  have hD : ∀ g, ∀ y ∈ N'.U ∩ B, N'.rep.Φ g y ∈ N'.U ∩ B := by
    intro g y hy
    refine ⟨N'.Φ_mem g hy.1, ?_⟩
    have hmem : N'.rep.Φ g y ∈ X.π ⁻¹' (X.π '' B) :=
      ⟨y, hy.2, (N'.π_Φ g (N'.U_subset hy.1)).symm⟩
    rwa [hB] at hmem
  -- Step 1: a neighbourhood `W(p)` of every orbit meeting only finitely many `|Ṽ_b|`
  have hW : ∀ p : X.OrbitSpace, ∃ W : Set X.OrbitSpace, IsOpen W ∧ p ∈ W ∧
      {b : A | (X.π '' V b ∩ W).Nonempty}.Finite := by
    intro p
    obtain ⟨t, ht, hfin⟩ := hlf p
    obtain ⟨W, hWt, hWo, hpW⟩ := mem_nhds_iff.1 ht
    exact ⟨W, hWo, hpW, hfin.subset fun b ⟨q, hq1, hq2⟩ => ⟨q, hq1, hWt hq2⟩⟩
  choose W hWo hpW hWfin using hW
  let F : X.OrbitSpace → Set Obj := fun p => Subtype.val '' {b : A | (X.π '' V b ∩ W p).Nonempty}
  have hFfin : ∀ p, (F p).Finite := fun p => (hWfin p).image _
  have hFA : ∀ p, F p ⊆ A := fun p => by
    rintro _ ⟨b, _, rfl⟩
    exact b.2
  -- Step 2: the properness neighbourhoods
  have hN : ∀ b ∈ A, ∀ y ∈ N'.U ∩ B, ∃ W' : Set Obj, IsOpen W' ∧ y ∈ W' ∧
      ∀ φ, X.src φ ∈ W' → X.tgt φ ∈ closure (Ut b) → φ ∈ O a b := by
    intro b hb y hy
    refine X.exists_nhds_of_isProperSubset (hprop b hb) (hOo b hb) fun φ hφs hφt => ?_
    refine hO b hb φ (hφs ▸ hy) ⟨hcl b hb hφt, ?_⟩
    exact IsSaturated.tgt_mem X hB (hφs ▸ hy.2)
  choose! Nb hNbo hyNb hNb using hN
  -- Step 3: `O₀(y)`
  let O₀ : Obj → Set Obj := fun y =>
    N'.U ∩ X.π ⁻¹' W (X.π y) ∩ ⋂ b ∈ F (X.π y), Nb b y
  have hO₀o : ∀ y ∈ N'.U ∩ B, IsOpen (O₀ y) := fun y hy =>
    (N'.isOpen_U.inter ((hWo _).preimage X.continuous_π)).inter
      ((hFfin _).isOpen_biInter fun b hb => hNbo b (hFA _ hb) y hy)
  have hyO₀ : ∀ y ∈ N'.U ∩ B, y ∈ O₀ y := fun y hy =>
    ⟨⟨hy.1, hpW _⟩, mem_iInter₂.2 fun b hb => hyNb b (hFA _ hb) y hy⟩
  -- Step 4: the symmetrization
  let Oy : Obj → Set Obj := fun y => ⋂ g, N'.U ∩ N'.rep.Φ g ⁻¹' O₀ (N'.rep.Φ g y)
  have hOyU : ∀ y, Oy y ⊆ N'.U := fun y z hz => (mem_iInter.1 hz 1).1
  have hOyO₀ : ∀ y ∈ N'.U, Oy y ⊆ O₀ y := fun y hy z hz => by
    have h := (mem_iInter.1 hz 1).2
    rwa [mem_preimage, N'.Φ_one (mem_iInter.1 hz 1).1, N'.Φ_one hy] at h
  have himage : ∀ g, ∀ y ∈ N'.U, N'.rep.Φ g '' Oy y = Oy (N'.rep.Φ g y) := by
    intro g y hy
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzU := hOyU y hz
      refine mem_iInter.2 fun h => ⟨N'.Φ_mem g hzU, ?_⟩
      rw [mem_preimage, ← N'.Φ_mul h g hzU, ← N'.Φ_mul h g hy]
      exact (mem_iInter.1 hz (h * g)).2
    · intro hw
      have hwU := hOyU _ hw
      refine ⟨N'.rep.Φ g⁻¹ w, mem_iInter.2 fun h => ⟨N'.Φ_mem g⁻¹ hwU, ?_⟩,
        N'.Φ_Φ_inv g hwU⟩
      have h1 := (mem_iInter.1 hw (h * g⁻¹)).2
      rw [mem_preimage, N'.Φ_mul h g⁻¹ hwU] at h1
      rw [mem_preimage]
      convert h1 using 2
      rw [N'.Φ_mul h g⁻¹ (N'.Φ_mem g hy), N'.Φ_inv_Φ g hy]
  refine ⟨fun y => F (X.π y), Oy, fun y hy => ⟨?_, ?_, hOyU y, hFfin _, hFA _, ?_, ?_, ?_⟩⟩
  · exact isOpen_iInter_of_finite fun g =>
      ((N'.rep.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn.mono N'.U_subset).isOpen_inter_preimage
        N'.isOpen_U (hO₀o _ (hD g y hy))
  · exact mem_iInter.2 fun g => ⟨hy.1, hyO₀ _ (hD g y hy)⟩
  · rintro b hb ⟨q, ⟨z, hz, rfl⟩, hq⟩
    refine ⟨⟨b, hb⟩, ⟨X.π z, hq, ?_⟩, rfl⟩
    exact (hOyO₀ y hy.1 hz).1.2
  · intro g
    refine ⟨himage g y hy.1, ?_⟩
    change F (X.π (N'.rep.Φ g y)) = F (X.π y)
    rw [N'.π_Φ g (N'.U_subset hy.1)]
  · intro b hb φ hφs hφt
    exact hNb b (hFA _ hb) y hy φ (mem_iInter₂.1 (hOyO₀ y hy.1 hφs).2 b hb) (subset_closure hφt)

/-- **Lemma 14.3.7, the `G_y`-invariance**: in the setting of `lemma_14_3_7`, `Õ(y)` is invariant
under the elements of `G_a` fixing `y` (whose natural action near `y` is that of `G_y`, since every
morphism between points of `Ũ'(a)` is a `Γ(g, ·)`). -/
theorem lemma_14_3_7_stab {a y : Obj} (N' : X.NatNbhd a) {Oy : Obj → Set Obj}
    (h : ∀ g, N'.rep.Φ g '' Oy y = Oy (N'.rep.Φ g y)) {g : X.Isotropy a}
    (hg : N'.rep.Φ g y = y) : MapsTo (N'.rep.Φ g) (Oy y) (Oy y) := by
  intro z hz
  have := mem_image_of_mem (N'.rep.Φ g) hz
  rwa [h g, hg] at this

/-! ### Lemma 14.5.1 -/

/-- **Lemma 14.5.1, p. 671 (2017: Lemma 14.10)** (partition of unity adapted to the `V̂_a`): let
`X` admit sc-smooth
partitions of unity (Definition 7.5.5), `B ⊆ X` closed and saturated (for `∂X`), `A ⊆ B`, and
`V̂_a` open with `B ⊆ ⋃_{a ∈ A} π⁻¹(π(V̂_a))`.  Then there are sc-smooth functions
`β_a : X → [0, 1]`, `a ∈ A`, invariant under morphisms (functors), with
(1) `supp β_a ⊆ π⁻¹(π(V̂_a))`,
(2) every `y` has a saturated open neighbourhood `Q(y)` on which only finitely many `β_a` are not
identically `0`, (3) `∑_{a ∈ A} β_a(y) = 1` for `y ∈ B`.  (Tameness of `X`, assumed in the text's
setting, is not used.) -/
theorem lemma_14_5_1 (hpu : X.HasScPartitionsOfUnity) {A B : Set Obj} (hB : IsClosed B)
    (hBs : X.IsSaturated B) (hAB : A ⊆ B) {V : Obj → Set Obj} (hV : ∀ a ∈ A, IsOpen (V a))
    (hcov : B ⊆ ⋃ a ∈ A, X.saturation (V a)) :
    ∃ β : Obj → Obj → ℝ,
      (∀ a ∈ A, X.PObj.IsScSmoothMap realPolyfold (β a)) ∧
      (∀ a y, β a y ∈ Icc (0 : ℝ) 1) ∧
      (∀ a φ, β a (X.src φ) = β a (X.tgt φ)) ∧
      (∀ a ∈ A, tsupport (β a) ⊆ X.saturation (V a)) ∧
      (∀ y, ∃ Q : Set Obj, IsOpen Q ∧ X.IsSaturated Q ∧ y ∈ Q ∧
        {a | a ∈ A ∧ ∃ q ∈ Q, β a q ≠ 0}.Finite) ∧
      (∀ y ∈ B, ∑ᶠ a ∈ A, β a y = 1) := by
  classical
  let U : Obj → Set Obj := fun x => if x ∈ A then X.saturation (V x) else Bᶜ
  have hUo : ∀ x, IsOpen (U x) := fun x => by
    by_cases hx : x ∈ A
    · simp only [U, if_pos hx]; exact X.isOpen_saturation (hV x hx)
    · simp only [U, if_neg hx]; exact hB.isOpen_compl
  have hUs : ∀ x, X.IsSaturated (U x) := fun x => by
    by_cases hx : x ∈ A
    · simp only [U, if_pos hx]; exact X.isSaturated_preimage_π _
    · simp only [U, if_neg hx]; exact X.isSaturated_compl hBs
  have hUc : ⋃ x, U x = univ := by
    refine eq_univ_of_forall fun y => ?_
    by_cases hy : y ∈ B
    · obtain ⟨a, ha, hya⟩ := mem_iUnion₂.1 (hcov hy)
      exact mem_iUnion.2 ⟨a, by simp only [U, if_pos ha]; exact hya⟩
    · exact mem_iUnion.2 ⟨y, by simp only [U, if_neg (fun h => hy (hAB h))]; exact hy⟩
  obtain ⟨ρ, hsub, hsm, hlf, hinv⟩ := hpu Obj U hUo hUs hUc
  have hzero : ∀ x ∉ A, ∀ y ∈ B, ρ x y = 0 := fun x hx y hy => by
    have h := hsub x
    simp only [U, if_neg hx] at h
    exact image_eq_zero_of_notMem_tsupport fun hy' => h hy' hy
  refine ⟨fun a => ρ a, fun a _ => hsm a, fun a y => ⟨ρ.nonneg a y, ρ.le_one a y⟩,
    fun a φ => hinv a φ, fun a ha => ?_, fun y => ?_, fun y hy => ?_⟩
  · have h := hsub a
    simp only [U, if_pos ha] at h
    exact h
  · obtain ⟨Q, hQo, hQs, hyQ, hQfin⟩ := hlf y
    refine ⟨Q, hQo, hQs, hyQ, hQfin.subset ?_⟩
    rintro a ⟨_, q, hq, hqa⟩
    exact ⟨q, hq, subset_tsupport _ hqa⟩
  · rw [finsum_mem_def, Set.indicator_eq_self.2]
    · exact ρ.sum_eq_one (mem_univ y)
    · intro x hx
      by_contra hxA
      exact hx (hzero x hxA y hy)

end EpGroupoid

end Polyfold
