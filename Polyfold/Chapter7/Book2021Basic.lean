import Polyfold.Chapter7.Basic
import Polyfold.Chapter7.NaturalRepFinite
import Polyfold.Chapter7.ProperSubsets
import Polyfold.Chapter7.NonVacuity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 7, §7.1 "Ep-Groupoids and Basic Properties" (pp. 291–304; 2017: pp. 228–236):
the remark after **Definition 7.1.7** (p. 291; 2017: Definition 7.7, pp. 228–229), the data
(7.3) and **Proposition 7.1.14** (p. 296, new in the 2021 edition), **Proposition 7.1.15**
(p. 297; 2017: Proposition 7.5, p. 233), **Lemma 7.1.16** (p. 300, new in the 2021 edition) and
**Corollary 7.1.17** (pp. 301–304, new in the 2021 edition).  Numbers and pages are the 2021
text's, the 2017 ones in parentheses.

# §7.1 in the 2021 edition: the changed and the new items

## The text, paraphrased

(Remark after Definition 7.1.7, p. 291 (2017: after Definition 7.7, pp. 228–229)) It suffices
that a functor `f` between ep-groupoids is sc-smooth between the object spaces and **continuous
(on level 0) between the morphism spaces**; the 2017 text asked only for the first condition.
Given `φ` and `ψ = f(φ)` there are open `U(φ)`, `U(ψ)`, `U(s(φ))`, `U(s(ψ))` with
`f(U(s(φ))) ⊂ U(s(ψ))`, `f(U(φ)) ⊂ U(ψ)`, both restrictions of `s` sc-diffeomorphisms, and
`f(γ) = (s|U(ψ))⁻¹(f(s(γ)))` on `U(φ)`.

(Before Proposition 7.1.14, (7.3), p. 296) Fix open neighbourhoods `W(x)` of `x` and `U^s(g)`,
`U^t(g)` of `g ∈ G_x` such that the restrictions `s_g : U^s(g) → W(x)`, `t_g : U^t(g) → W(x)` of
`s` and `t` are sc-diffeomorphisms.  (Proposition 7.1.14) If `Φ : G_x → Diff_sc(U(x))` is a
homomorphism and `Γ` has the properties (1)–(3) of Theorem 7.1.13, there is a `Φ`-invariant open
neighbourhood `V(x) ⊂ W(x) ∩ U(x)` with `Γ(g, v) = s_g⁻¹(v)` and `Φ(g)(v) = t_g ∘ s_g⁻¹(v)` for
`v ∈ V(x)`; the proof also gives `Γ(g, v) = t_g⁻¹(Φ(g)(v))`.  So the natural representation is
essentially unique.

(Proposition 7.1.15, p. 297 (2017: Proposition 7.5)) As 2017 Proposition 7.5, with (2) now
`s : 𝐔(ψ) → U(s(ψ))` and `t : 𝐔(ψ) → U(t(ψ))` (2017: both into `U(y)`), with `ψ ∈ 𝐔(ψ)`, and
with the addition "`t(ψ') = f(ψ)(s(ψ'))` for `ψ' ∈ 𝐔(ψ)`".

(Lemma 7.1.16, p. 300) For `ψ ∈ 𝐘` and a sequence `ψ'_k ∈ 𝐔(ψ)` converging to `ψ' ∈ 𝐗`: if
`(s(ψ'_k))` or `(t(ψ'_k))` converges to an object of `U(s(ψ))` or of `U(t(ψ))`, then
`ψ' ∈ 𝐔(ψ)`, `s(ψ'_k) → s(ψ') ∈ U(s(ψ))` and `t(ψ'_k) → t(ψ') ∈ U(t(ψ))`.

(Corollary 7.1.17, pp. 301–304) (4) For `x ∈ Y`, `g ∈ G_x`: `f(g)(z) = t ∘ Γ(g, z) = g ∗ z`.
(5) `f(φ)` is equivariant for `γ_φ(g) = φ ∘ g ∘ φ⁻¹`.  (6) For `s(ψ) = t(φ)` the multiplication
`(ψ', φ') ↦ ψ' ∘ φ'` is an sc-diffeomorphism `𝐔(ψ) ₛ×ₜ 𝐔(φ) → 𝐔(ψ ∘ φ)`; the proof shows that
`P(ψ', φ') = s(φ')` is an sc-diffeomorphism onto `U(s(φ))`, that the image of the multiplication
is connected and lies in `𝐔(ψ ∘ φ)` (by Lemma 7.1.16), and writes the multiplication as `R ∘ P`.
(7) The `U(x)` may be taken with the properness property.

## What is formalized

* `remark_definition_7_1_7` (**the remark after Definition 7.1.7**): for a functor sc-smooth on objects
  and continuous on morphisms, the four neighbourhoods, the two sc-diffeomorphisms, the formula,
  and sc-smoothness on morphisms.  `remark_definition_7_1_7_remarkFunctor`: the functor
  `Examples.remarkFunctor` (the counterexample to the 2017 remark,
  `remark_definition_7_1_7_counterexample`) is excluded by the 2021 hypothesis.
* `IsotropySheetData` (the data **(7.3)**), with the witness `exists_isotropySheetData` (for every
  object of every ep-groupoid); `proposition_7_1_14` (**Proposition 7.1.14**) and
  `proposition_7_1_14_of_naturalRep` (for the project's `NaturalRep`).
* `proposition_7_1_15` (**Proposition 7.1.15**).  `src_eq_tgt_of_printed_2017` and
  `not_printed_2017_reflection`: 2017 Proposition 7.5 (2) as printed (`s` and `t` of `𝐔(ψ)` both
  into one `U(y)`) forces `s(ψ) = t(ψ)` for every `ψ ∈ 𝐘`, so it cannot hold as we read it once
  `Y` has two distinct objects; in `ℤ/2 ⋉ ℝ` with `Y = {1, −1}` the hypotheses hold, a
  `NaturalRepFinite` (the 2021 reading) exists, and no data of the 2017 printed reading exists.
* `lemma_7_1_16` (**Lemma 7.1.16**).
* `corollary_7_1_17_4`, `corollary_7_1_17_5`, `corollary_7_1_17_6`,
  `corollary_7_1_17_7` (**Corollary 7.1.17 (4)–(7)**).

## What the text leaves implicit, and the choices made

* Proposition 7.1.15 is the project's `NaturalRepFinite` (Definition 7.1.18; 2017: Definition 7.8)
  produced by `proposition_7_1_15_of_mem_nhdsSet`; its field `isScDiffeoOn_src`/`isScDiffeoOn_tgt`
  was already the 2021 form of (2).  The decomposition "into connected components" is
  `NatRepFinite.connectedComponentIn_morOn`.
* (7.3): "open neighbourhoods `U^s(g)`, `U^t(g)` for `g`" is read as neighbourhoods **of** `g`
  (`g ∈ U^s(g) ∩ U^t(g)`); without `g ∈ U^s(g)` the conclusion `Γ(g, x) = g = s_g⁻¹(x)` fails.
  `t_g ∘ s_g⁻¹` is `t ∘ s_g⁻¹` (the value lies in `U^t(g)` by the proof).
* Proposition 7.1.14 is stated with the hypotheses as printed (an open `U(x) ∋ x`, `Φ(g)` an
  sc-diffeomorphism of `U(x)` with inverse `Φ(g⁻¹)`, `Φ` multiplicative, `Γ` with (1)–(3)); the
  project's `NaturalRep` adds connectedness of `U(x)`, which the proof does not use.  "Invariant
  under `Φ`" is `Φ(g)(V(x)) ⊆ V(x)` for all `g`.
* Lemma 7.1.16: "converges to some object in either `U(s(ψ))` or `U(t(ψ))`" is read literally,
  four cases; the two crossed cases reduce to the direct ones because the `U(y)` are disjoint
  and open.  Sequences are `ℕ → 𝐗` with `Filter.Tendsto … atTop`.
* Corollary 7.1.17 (4): `Γ` is that of a natural representation `R` of `G_x` on `U(x)` with
  `R.Φ g = f(g)` (the field `natural`); we prove `Γ(g, z) = (s|𝐔(g))⁻¹(z)` (as in the text's
  proof), `f(g)(z) = t(Γ(g, z))` and `t(Γ(g, z)) = g ∗ z`.  The argument for the first identity
  is topological (the image of the connected `U(x)` under `Γ(g, ·)` lies in one component),
  since `f(ψ) = f(ψ')` does not force `ψ = ψ'` in a non-effective ep-groupoid.
* (5) is stated with the conjugation `conjIsotropy φ : G_{s(φ)} ≃* G_{t(φ)}` and the action
  `z ↦ f(g)(z)` (by (4) the natural action).
* (6): `𝐔(ψ) ₛ×ₜ 𝐔(φ)` is the open subset of the fibred product sub-M-polyfold
  `𝐗 ₛ×ₜ 𝐗 ⊆ 𝐗 × 𝐗` (Part I's `MPolyfold.isSubMPolyfold_fibredProduct`, the M-polyfold of
  Definition 7.1.3 (4)).  The sc-diffeomorphism is proved as `(s|𝐔(ψ∘φ))⁻¹ ∘ s ∘ π₂`, which equals
  the multiplication once its image is known to lie in `𝐔(ψ ∘ φ)`; this last point uses the
  connectedness of `𝐔(ψ) ₛ×ₜ 𝐔(φ)` and the continuity of the multiplication, as in the text,
  without sequences.
* (7): for every neighbourhood `V` of `Y` there is a natural representation on neighbourhoods in
  `V` all of whose `U(y)` have the properness property (Definition 7.5.8; 2017: Definition 7.17).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

namespace Polyfold

namespace EpGroupoid

universe u v

/-- Only the values of `f` on `U` matter for an sc-diffeomorphism `f : U → V` (a local copy of
`MPolyfold.IsScDiffeoOn.congr_left` of Chapter 8, not imported here). -/
private theorem isScDiffeoOn_congr_left_b21 {A B : Type*} [TopologicalSpace A] [T2Space A]
    [ParacompactSpace A] [TopologicalSpace B] [T2Space B] [ParacompactSpace B] {P : MPolyfold A}
    {Q : MPolyfold B} {f f' : A → B} {g : B → A} {U : Set A} {V : Set B}
    (h : P.IsScDiffeoOn Q f g U V) (hff' : EqOn f f' U) : P.IsScDiffeoOn Q f' g U V where
  isScSmoothOn := h.isScSmoothOn.congr hff'
  isScSmoothOn_inv := h.isScSmoothOn_inv
  mapsTo x hx := hff' hx ▸ h.mapsTo hx
  mapsTo_inv := h.mapsTo_inv
  left_inv x hx := by rw [← hff' hx]; exact h.left_inv x hx
  right_inv y hy := by rw [← hff' (h.mapsTo_inv hy)]; exact h.right_inv y hy

/-! ### The remark after Definition 7.1.7 -/

section Remark

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- **The remark after 2021 Definition 7.1.7**, p. 291 (2017: after Definition 7.7, corrected in
2021): for a functor `f` sc-smooth on the object spaces and continuous on the morphism spaces,
and `φ ∈ 𝐗`, `ψ = f(φ)`, there are open `U(φ) ∋ φ`, `U(ψ) ∋ ψ`, `U(s(φ))`, `U(s(ψ))` with
`f(U(s(φ))) ⊆ U(s(ψ))`, `f(U(φ)) ⊆ U(ψ)`, `s : U(φ) → U(s(φ))` and `s : U(ψ) → U(s(ψ))`
sc-diffeomorphisms, and `f(γ) = (s|U(ψ))⁻¹(f(s(γ)))` for `γ ∈ U(φ)`; hence `f` is sc-smooth on
the morphism spaces. -/
theorem remark_definition_7_1_7 {F : GroupoidFunctor X.toGroupoidStr Y.toGroupoidStr}
    (hobj : X.PObj.IsScSmoothMap Y.PObj F.obj) (hmor : Continuous F.mor) (φ : Mor) :
    ∃ (Uφ : Set Mor) (Uψ : Set Mor') (Usφ : Set Obj) (Usψ : Set Obj') (σφ : Obj → Mor)
      (σψ : Obj' → Mor'),
      φ ∈ Uφ ∧ F.mor φ ∈ Uψ ∧ F.obj '' Usφ ⊆ Usψ ∧ F.mor '' Uφ ⊆ Uψ ∧
      X.PMor.IsScDiffeoOn X.PObj X.src σφ Uφ Usφ ∧
      Y.PMor.IsScDiffeoOn Y.PObj Y.src σψ Uψ Usψ ∧
      (∀ γ ∈ Uφ, F.mor γ = σψ (F.obj (X.src γ))) ∧
      X.PMor.IsScSmoothMap Y.PMor F.mor := by
  obtain ⟨W', V', σψ, hψ, hd'⟩ := Y.isLocalScDiffeo_src (F.mor φ)
  obtain ⟨W, V, σφ, hφ, hd⟩ := X.isLocalScDiffeo_src φ
  have hO : IsOpen (W ∩ F.mor ⁻¹' W') :=
    hd.isScSmoothOn.isOpen.inter (hd'.isScSmoothOn.isOpen.preimage hmor)
  refine ⟨W ∩ F.mor ⁻¹' W', W', V ∩ σφ ⁻¹' (W ∩ F.mor ⁻¹' W'), V', σφ, σψ, ⟨hφ, hψ⟩, hψ,
    ?_, ?_, hd.restrict hO inter_subset_left, hd', fun γ hγ => mor_eq_srcInv_obj_src F hd' hγ.2,
    isScSmoothMap_mor_of_continuous hobj hmor⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hγ : F.mor (σφ z) ∈ W' := hz.2.2
    have h1 := hd'.mapsTo hγ
    rwa [F.src_mor, hd.right_inv z hz.1] at h1
  · rintro _ ⟨γ, hγ, rfl⟩
    exact hγ.2

/-- The 2017 counterexample `Examples.remarkFunctor` (sc-smooth on the objects of `ℤ/3 × ℝ ⇉ ℝ`,
not an `EP` morphism) **does not satisfy the hypothesis of the 2021 remark**: it is not continuous
on the morphism spaces. -/
theorem remark_definition_7_1_7_remarkFunctor :
    Examples.trivialZ3EpGroupoid.PObj.IsScSmoothMap Examples.trivialZ3EpGroupoid.PObj
      Examples.remarkFunctor.obj ∧ ¬ Continuous Examples.remarkFunctor.mor :=
  ⟨Examples.isScSmoothMap_remarkFunctor_obj, Examples.not_continuous_remarkFunctor_mor⟩

end Remark

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### The data (7.3) and Proposition 7.1.14 -/

/-- **The data (7.3)** before 2021 Proposition 7.1.14, p. 296 (new in the 2021 edition): an open
neighbourhood `W(x)` of `x` and, for every `g ∈ G_x`, open neighbourhoods `U^s(g)`, `U^t(g)` of
`g` on which `s_g = s|U^s(g) : U^s(g) → W(x)` and `t_g = t|U^t(g) : U^t(g) → W(x)` are
sc-diffeomorphisms, with inverses `s_g⁻¹`, `t_g⁻¹`.  (`W(x)` is open as the target of an
sc-diffeomorphism.) -/
structure IsotropySheetData (x : Obj) where
  /-- `W(x)`. -/
  W : Set Obj
  /-- `U^s(g)`. -/
  srcSheet : X.Isotropy x → Set Mor
  /-- `U^t(g)`. -/
  tgtSheet : X.Isotropy x → Set Mor
  /-- `s_g⁻¹ : W(x) → U^s(g)`. -/
  srcInv : X.Isotropy x → Obj → Mor
  /-- `t_g⁻¹ : W(x) → U^t(g)`. -/
  tgtInv : X.Isotropy x → Obj → Mor
  mem_W : x ∈ W
  mem_srcSheet : ∀ g, g.val ∈ srcSheet g
  mem_tgtSheet : ∀ g, g.val ∈ tgtSheet g
  isScDiffeoOn_src : ∀ g, X.PMor.IsScDiffeoOn X.PObj X.src (srcInv g) (srcSheet g) W
  isScDiffeoOn_tgt : ∀ g, X.PMor.IsScDiffeoOn X.PObj X.tgt (tgtInv g) (tgtSheet g) W

/-- **The data (7.3) exist** at every object of every ep-groupoid: `W(x)` is the intersection of
the source and target sets of sheets at the finitely many `g ∈ G_x`. -/
theorem exists_isotropySheetData (x : Obj) : Nonempty (X.IsotropySheetData x) := by
  choose S hS using fun g : X.Isotropy x => X.exists_sheet g.val
  set W := ⋂ g, ((S g).srcSet ∩ (S g).tgtSet) with hWdef
  have hWo : IsOpen W := isOpen_iInter_of_finite fun g =>
    (S g).isScDiffeoOn_src.isOpen_target.inter (S g).isScDiffeoOn_tgt.isOpen_target
  have hxW : x ∈ W := mem_iInter.2 fun g => by
    have h1 := (S g).isScDiffeoOn_src.mapsTo (hS g)
    have h2 := (S g).isScDiffeoOn_tgt.mapsTo (hS g)
    rw [g.src_val] at h1
    rw [g.tgt_val] at h2
    exact ⟨h1, h2⟩
  have hWs : ∀ g, W ⊆ (S g).srcSet := fun g => (iInter_subset _ g).trans inter_subset_left
  have hWt : ∀ g, W ⊆ (S g).tgtSet := fun g => (iInter_subset _ g).trans inter_subset_right
  exact ⟨{ W := W
           srcSheet := fun g => (S g).carrier ∩ X.src ⁻¹' W
           tgtSheet := fun g => (S g).carrier ∩ X.tgt ⁻¹' W
           srcInv := fun g => (S g).srcInv
           tgtInv := fun g => (S g).tgtInv
           mem_W := hxW
           mem_srcSheet := fun g => ⟨hS g, by rw [mem_preimage, g.src_val]; exact hxW⟩
           mem_tgtSheet := fun g => ⟨hS g, by rw [mem_preimage, g.tgt_val]; exact hxW⟩
           isScDiffeoOn_src := fun g => ((S g).isScDiffeoOn_src.symm.restrict hWo (hWs g)).symm
           isScDiffeoOn_tgt := fun g =>
             ((S g).isScDiffeoOn_tgt.symm.restrict hWo (hWt g)).symm }⟩

/-- **2021 Proposition 7.1.14**, p. 296 (new in the 2021 edition): let `U(x)` be an open
neighbourhood of `x`, `Φ : G_x → Diff_sc(U(x))` a homomorphism (`Φ(g)` an sc-diffeomorphism of
`U(x)` with inverse `Φ(g⁻¹)`, `Φ(gh) = Φ(g) ∘ Φ(h)`) and `Γ` with the properties (1)–(3) of
Theorem 7.1.13, and fix the data (7.3).  Then there is an open `Φ`-invariant `V(x) ∋ x`,
`V(x) ⊆ W(x) ∩ U(x)`, with `Γ(g, v) = s_g⁻¹(v)` and `Φ(g)(v) = t ∘ s_g⁻¹(v)` for `v ∈ V(x)`,
`g ∈ G_x`; also `Γ(g, v) = t_g⁻¹(Φ(g)(v))` (from the proof, (7.4)).  Property (3) of
Theorem 7.1.13 is not used. -/
theorem proposition_7_1_14 {x : Obj} {U : Set Obj} (hU : IsOpen U) (hxU : x ∈ U)
    (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor)
    (hΦ : ∀ g, X.PObj.IsScDiffeoOn X.PObj (Φ g) (Φ g⁻¹) U U)
    (hΦmul : ∀ g h, ∀ y ∈ U, Φ (g * h) y = Φ g (Φ h y))
    (hΓ : ∀ g, X.PObj.IsScSmoothOn X.PMor (Γ g) U)
    (hΓx : ∀ g, Γ g x = g.val) (hsΓ : ∀ g, ∀ y ∈ U, X.src (Γ g y) = y)
    (htΓ : ∀ g, ∀ y ∈ U, X.tgt (Γ g y) = Φ g y)
    (_hΓ3 : ∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g, Γ g (X.src h) = h)
    (D : X.IsotropySheetData x) :
    ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧ V ⊆ D.W ∩ U ∧ (∀ g, MapsTo (Φ g) V V) ∧
      ∀ g, ∀ v ∈ V, Γ g v = D.srcInv g v ∧ Φ g v = X.tgt (D.srcInv g v) ∧
        Γ g v = D.tgtInv g (Φ g v) := by
  have hΦ1 : ∀ y ∈ U, Φ 1 y = y := fun y hy => by
    have h1 := (hΦ 1).left_inv y hy
    rw [inv_one] at h1
    have h2 := hΦmul 1 1 y hy
    rw [mul_one] at h2
    rw [h2]
    exact h1
  have hΦx : ∀ g, Φ g x = x := fun g => by
    rw [← htΓ g x hxU, hΓx]
    exact g.tgt_val
  -- `N_g = {v ∈ U | Γ(g, v) ∈ U^s(g) ∩ U^t(g)}` and `N = W ∩ ⋂_g N_g`
  set N := D.W ∩ ⋂ g, (U ∩ Γ g ⁻¹' (D.srcSheet g ∩ D.tgtSheet g)) with hNdef
  have hNo : IsOpen N := (D.isScDiffeoOn_src 1).isOpen_target.inter
    (isOpen_iInter_of_finite fun g => (hΓ g).continuousOn.isOpen_inter_preimage hU
      ((D.isScDiffeoOn_src g).isOpen_source.inter (D.isScDiffeoOn_tgt g).isOpen_source))
  have hxN : x ∈ N := ⟨D.mem_W, mem_iInter.2 fun g =>
    ⟨hxU, by rw [mem_preimage, hΓx]; exact ⟨D.mem_srcSheet g, D.mem_tgtSheet g⟩⟩⟩
  -- `V = ⋂_g Φ(g)⁻¹(N)`
  set V := ⋂ g, (U ∩ Φ g ⁻¹' N) with hVdef
  have hVo : IsOpen V := isOpen_iInter_of_finite fun g =>
    (hΦ g).isScSmoothOn.continuousOn.isOpen_inter_preimage hU hNo
  have hVU : V ⊆ U := fun v hv => (mem_iInter.1 hv 1).1
  have hVN : V ⊆ N := fun v hv => by
    have h1 := (mem_iInter.1 hv 1).2
    rwa [mem_preimage, hΦ1 v (hVU hv)] at h1
  refine ⟨V, hVo, mem_iInter.2 fun g => ⟨hxU, by rw [mem_preimage, hΦx]; exact hxN⟩,
    fun v hv => ⟨(hVN hv).1, hVU hv⟩, fun h v hv => mem_iInter.2 fun g =>
      ⟨(hΦ h).mapsTo (hVU hv), by
        rw [mem_preimage, ← hΦmul g h v (hVU hv)]
        exact (mem_iInter.1 hv (g * h)).2⟩, fun g v hv => ?_⟩
  have hmem : Γ g v ∈ D.srcSheet g ∩ D.tgtSheet g := (mem_iInter.1 (hVN hv).2 g).2
  have e1 : Γ g v = D.srcInv g v := by
    have h1 := (D.isScDiffeoOn_src g).left_inv _ hmem.1
    rw [hsΓ g v (hVU hv)] at h1
    exact h1.symm
  refine ⟨e1, ?_, ?_⟩
  · rw [← e1, htΓ g v (hVU hv)]
  · have h1 := (D.isScDiffeoOn_tgt g).left_inv _ hmem.2
    rw [htΓ g v (hVU hv)] at h1
    exact h1.symm

/-- **2021 Proposition 7.1.14** for a natural representation in the project's sense
(`NaturalRep`, the data of Theorem 7.1.13). -/
theorem proposition_7_1_14_of_naturalRep {x : Obj} (R : X.NaturalRep x)
    (D : X.IsotropySheetData x) :
    ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧ V ⊆ D.W ∩ R.U ∧ (∀ g, MapsTo (R.Φ g) V V) ∧
      ∀ g, ∀ v ∈ V, R.Γ g v = D.srcInv g v ∧ R.Φ g v = X.tgt (D.srcInv g v) ∧
        R.Γ g v = D.tgtInv g (R.Φ g v) :=
  X.proposition_7_1_14 R.isOpen_U R.mem_U R.Φ R.Γ R.isScDiffeoOn_Φ R.Φ_mul R.isScSmoothOn_Γ
    R.Γ_self R.src_Γ R.tgt_Γ R.existsUnique_Γ D

/-! ### Proposition 7.1.15 -/

/-- **2021 Proposition 7.1.15**, p. 297 (2017: Proposition 7.5, with (2) corrected): for a finite
set `Y` of mutually isomorphic objects and a neighbourhood `V` of `Y` there is a natural
representation `f` of `Y` on neighbourhoods in `V` (`NaturalRepFinite`: disjoint connected open
`U(y) ⊆ V`, the functor `f`, (1) the natural action), such that the morphisms between points of
`U = ⋃ U(y)` decompose into the connected components `𝐔(ψ) ∋ ψ`, `ψ ∈ 𝐘`, (2) `s : 𝐔(ψ) → U(s(ψ))`
and `t : 𝐔(ψ) → U(t(ψ))` are sc-diffeomorphisms, (3) `f(ψ) = t ∘ (s|𝐔(ψ))⁻¹` on `U(s(ψ))`, and
`t(ψ') = f(ψ)(s(ψ'))` for `ψ' ∈ 𝐔(ψ)`. -/
theorem proposition_7_1_15 (Y : Finset Obj) (hY : ∀ y ∈ Y, ∀ y' ∈ Y, X.Isomorphic y y')
    {V : Set Obj} (hV : V ∈ 𝓝ˢ (Y : Set Obj)) :
    ∃ N : X.NaturalRepFinite Y V,
      (∀ ψ ∈ X.morOn (Y : Set Obj), ψ ∈ N.sheet ψ ∧
        connectedComponentIn (X.morOn (⋃ y ∈ Y, N.U y)) ψ = N.sheet ψ) ∧
      (∀ ψ ∈ X.morOn (Y : Set Obj),
        X.PMor.IsScDiffeoOn X.PObj X.src (N.srcInv ψ) (N.sheet ψ) (N.U (X.src ψ)) ∧
        ∃ τ, X.PMor.IsScDiffeoOn X.PObj X.tgt τ (N.sheet ψ) (N.U (X.tgt ψ))) ∧
      (∀ ψ ∈ X.morOn (Y : Set Obj), ∀ z ∈ N.U (X.src ψ), N.F ψ z = X.tgt (N.srcInv ψ z)) ∧
      (∀ ψ ∈ X.morOn (Y : Set Obj), ∀ ψ' ∈ N.sheet ψ, X.tgt ψ' = N.F ψ (X.src ψ')) := by
  obtain ⟨N⟩ := X.proposition_7_1_15_of_mem_nhdsSet Y hY hV
  refine ⟨N, fun ψ hψ => ⟨N.mem_sheet ψ hψ,
    NatRepFinite.connectedComponentIn_morOn N hψ (N.mem_sheet ψ hψ)⟩,
    fun ψ hψ => ⟨N.isScDiffeoOn_src ψ hψ, N.isScDiffeoOn_tgt ψ hψ⟩, N.F_eq,
    fun ψ hψ ψ' hψ' => ?_⟩
  have hs := N.isScDiffeoOn_src ψ hψ
  rw [N.F_eq ψ hψ _ (hs.mapsTo hψ'), hs.left_inv ψ' hψ']

/-- **2017 Proposition 7.5 (2) as printed** (`s : 𝐔(ψ) → U(y)` and `t : 𝐔(ψ) → U(y)`, read with
one `y ∈ Y` for both maps; only `MapsTo` is used) together with the other requirements
(`y ∈ U(y)`, disjointness, the decomposition of the morphisms between points of `⋃ U(y)`) forces
`s(ψ) = t(ψ)` for every `ψ ∈ 𝐘`. -/
theorem src_eq_tgt_of_printed_2017 {Y : Finset Obj} (U : Obj → Set Obj) (sheet : Mor → Set Mor)
    (hmem : ∀ y ∈ Y, y ∈ U y) (hdisj : (Y : Set Obj).PairwiseDisjoint U)
    (hmor : X.morOn (⋃ y ∈ Y, U y) = ⋃ ψ ∈ X.morOn (Y : Set Obj), sheet ψ)
    (h2 : ∀ ψ ∈ X.morOn (Y : Set Obj), ∃ y ∈ Y,
      MapsTo X.src (sheet ψ) (U y) ∧ MapsTo X.tgt (sheet ψ) (U y))
    {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) : X.src ψ = X.tgt ψ := by
  have hs : X.src ψ ∈ Y := hψ.1
  have ht : X.tgt ψ ∈ Y := hψ.2
  have h : ψ ∈ X.morOn (⋃ y ∈ Y, U y) :=
    ⟨mem_biUnion hs (hmem _ hs), mem_biUnion ht (hmem _ ht)⟩
  rw [hmor] at h
  obtain ⟨ψ'', hψ'', hmem''⟩ := mem_iUnion₂.1 h
  obtain ⟨y, hy, hsy, hty⟩ := h2 ψ'' hψ''
  have e1 : X.src ψ = y := hdisj.elim_set hs hy _ (hmem _ hs) (hsy hmem'')
  have e2 : X.tgt ψ = y := hdisj.elim_set ht hy _ (hmem _ ht) (hty hmem'')
  rw [e1, e2]

/-- **2017 Proposition 7.5 (2) as printed does not hold as we read it**, witnessed by
`ℤ/2 ⋉ ℝ` (`Examples.reflectionEpGroupoid`) and `Y = {1, −1}`: the hypotheses of the proposition
hold, a natural representation in the 2021 reading exists, but no data of the 2017 printed
reading exist (the morphism `(−1, 1) : 1 → −1` has `s ≠ t`). -/
theorem not_printed_2017_reflection :
    (∀ y ∈ ({1, -1} : Finset (Fin 1 → ℝ)), ∀ y' ∈ ({1, -1} : Finset (Fin 1 → ℝ)),
      Examples.reflectionEpGroupoid.Isomorphic y y') ∧
    Nonempty (Examples.reflectionEpGroupoid.NaturalRepFinite ({1, -1} : Finset (Fin 1 → ℝ))
      univ) ∧
    ¬ ∃ (U : (Fin 1 → ℝ) → Set (Fin 1 → ℝ)) (sheet : ℤˣ × (Fin 1 → ℝ) → Set (ℤˣ × (Fin 1 → ℝ))),
      (∀ y ∈ ({1, -1} : Finset (Fin 1 → ℝ)), y ∈ U y) ∧
      (({1, -1} : Finset (Fin 1 → ℝ)) : Set (Fin 1 → ℝ)).PairwiseDisjoint U ∧
      Examples.reflectionEpGroupoid.morOn (⋃ y ∈ ({1, -1} : Finset (Fin 1 → ℝ)), U y) =
        ⋃ ψ ∈ Examples.reflectionEpGroupoid.morOn
          (({1, -1} : Finset (Fin 1 → ℝ)) : Set (Fin 1 → ℝ)), sheet ψ ∧
      ∀ ψ ∈ Examples.reflectionEpGroupoid.morOn
          (({1, -1} : Finset (Fin 1 → ℝ)) : Set (Fin 1 → ℝ)),
        ∃ y ∈ ({1, -1} : Finset (Fin 1 → ℝ)),
          MapsTo Examples.reflectionEpGroupoid.src (sheet ψ) (U y) ∧
          MapsTo Examples.reflectionEpGroupoid.tgt (sheet ψ) (U y) := by
  have hne : (1 : Fin 1 → ℝ) ≠ -1 := fun h => by
    have := congrFun h 0
    norm_num at this
  have hneg : ∀ y : Fin 1 → ℝ, Examples.reflectionEpGroupoid.Isomorphic y (-y) :=
    fun y => ⟨((-1 : ℤˣ), y), rfl, Examples.units_smul_rn_neg_one y⟩
  have hY : ∀ y ∈ ({1, -1} : Finset (Fin 1 → ℝ)), ∀ y' ∈ ({1, -1} : Finset (Fin 1 → ℝ)),
      Examples.reflectionEpGroupoid.Isomorphic y y' := by
    intro y hy y' hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy hy'
    rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact Examples.reflectionEpGroupoid.isomorphic_refl _
    · exact hneg 1
    · simpa using hneg (-1)
    · exact Examples.reflectionEpGroupoid.isomorphic_refl _
  refine ⟨hY, Examples.reflectionEpGroupoid.proposition_7_1_15_2017 _ hY isOpen_univ (subset_univ _), ?_⟩
  rintro ⟨U, sheet, hmem, hdisj, hmor, h2⟩
  have hψ : ((-1 : ℤˣ), (1 : Fin 1 → ℝ)) ∈ Examples.reflectionEpGroupoid.morOn
      (({1, -1} : Finset (Fin 1 → ℝ)) : Set (Fin 1 → ℝ)) := by
    refine ⟨by simp [Examples.reflectionEpGroupoid], ?_⟩
    change (-1 : ℤˣ) • (1 : Fin 1 → ℝ) ∈ (({1, -1} : Finset (Fin 1 → ℝ)) : Set (Fin 1 → ℝ))
    rw [Examples.units_smul_rn_neg_one]
    simp
  have := Examples.reflectionEpGroupoid.src_eq_tgt_of_printed_2017 U sheet hmem hdisj hmor h2 hψ
  change (1 : Fin 1 → ℝ) = (-1 : ℤˣ) • (1 : Fin 1 → ℝ) at this
  rw [Examples.units_smul_rn_neg_one] at this
  exact hne this

/-! ### Lemma 7.1.16 -/

variable {X}

/-- If a sequence of `U(a)` converges to a point of `U(b)` (`a, b ∈ Y`), the point lies in `U(a)`:
the `U(y)` are open and mutually disjoint. -/
theorem NaturalRepFinite.mem_U_of_tendsto {Y : Finset Obj} {V : Set Obj}
    (N : X.NaturalRepFinite Y V) {a b : Obj} (ha : a ∈ Y) (hb : b ∈ Y) {u : ℕ → Obj}
    (hu : ∀ k, u k ∈ N.U a) {z : Obj} (hz : z ∈ N.U b) (hlim : Tendsto u atTop (𝓝 z)) :
    z ∈ N.U a := by
  by_cases hab : a = b
  · subst hab
    exact hz
  · obtain ⟨k, hk⟩ := (hlim.eventually ((N.isOpen_U b hb).mem_nhds hz)).exists
    exact absurd (N.pairwiseDisjoint_U.elim_set ha hb _ (hu k) hk) hab

/-- **2021 Lemma 7.1.16**, p. 300 (new in the 2021 edition): for `ψ ∈ 𝐘` and a sequence
`ψ'_k ∈ 𝐔(ψ)` converging to `ψ' ∈ 𝐗`, if `(s(ψ'_k))` or `(t(ψ'_k))` converges to an object of
`U(s(ψ))` or of `U(t(ψ))`, then `ψ' ∈ 𝐔(ψ)`, and `s(ψ'_k) → s(ψ') ∈ U(s(ψ))`,
`t(ψ'_k) → t(ψ') ∈ U(t(ψ))`. -/
theorem lemma_7_1_16 {Y : Finset Obj} {V : Set Obj} (N : X.NaturalRepFinite Y V) {ψ : Mor}
    (hψ : ψ ∈ X.morOn (Y : Set Obj)) {ψs : ℕ → Mor} (hψs : ∀ k, ψs k ∈ N.sheet ψ) {ψ' : Mor}
    (hlim : Tendsto ψs atTop (𝓝 ψ'))
    (hconv : ∃ z ∈ N.U (X.src ψ) ∪ N.U (X.tgt ψ),
      Tendsto (fun k => X.src (ψs k)) atTop (𝓝 z) ∨ Tendsto (fun k => X.tgt (ψs k)) atTop (𝓝 z)) :
    ψ' ∈ N.sheet ψ ∧
      Tendsto (fun k => X.src (ψs k)) atTop (𝓝 (X.src ψ')) ∧ X.src ψ' ∈ N.U (X.src ψ) ∧
      Tendsto (fun k => X.tgt (ψs k)) atTop (𝓝 (X.tgt ψ')) ∧ X.tgt ψ' ∈ N.U (X.tgt ψ) := by
  have hsY : X.src ψ ∈ Y := hψ.1
  have htY : X.tgt ψ ∈ Y := hψ.2
  have hs := N.isScDiffeoOn_src ψ hψ
  obtain ⟨τ, ht⟩ := N.isScDiffeoOn_tgt ψ hψ
  have hmem : ψ' ∈ N.sheet ψ := by
    obtain ⟨z, hz, hsz | htz⟩ := hconv
    · have hz' : z ∈ N.U (X.src ψ) := hz.elim id fun hz =>
        N.mem_U_of_tendsto hsY htY (fun k => hs.mapsTo (hψs k)) hz hsz
      have hc : ContinuousAt (N.srcInv ψ) z :=
        hs.isScSmoothOn_inv.continuousOn.continuousAt ((N.isOpen_U _ hsY).mem_nhds hz')
      have h1 : Tendsto ψs atTop (𝓝 (N.srcInv ψ z)) :=
        (hc.tendsto.comp hsz).congr fun k => hs.left_inv _ (hψs k)
      rw [tendsto_nhds_unique hlim h1]
      exact hs.mapsTo_inv hz'
    · have hz' : z ∈ N.U (X.tgt ψ) := hz.elim (fun hz =>
        N.mem_U_of_tendsto htY hsY (fun k => ht.mapsTo (hψs k)) hz htz) id
      have hc : ContinuousAt τ z :=
        ht.isScSmoothOn_inv.continuousOn.continuousAt ((N.isOpen_U _ htY).mem_nhds hz')
      have h1 : Tendsto ψs atTop (𝓝 (τ z)) :=
        (hc.tendsto.comp htz).congr fun k => ht.left_inv _ (hψs k)
      rw [tendsto_nhds_unique hlim h1]
      exact ht.mapsTo_inv hz'
  exact ⟨hmem, (X.continuous_src.tendsto ψ').comp hlim, hs.mapsTo hmem,
    (X.continuous_tgt.tendsto ψ').comp hlim, ht.mapsTo hmem⟩

/-! ### Corollary 7.1.17 -/

/-- **2021 Corollary 7.1.17 (4)**, p. 301 (new in the 2021 edition): for `x ∈ Y` there is a
natural representation `(Φ, Γ)` of `G_x` on `U(x)` with `Φ(g) = f(g)` (property (1)), and for
`g ∈ G_x`, `z ∈ U(x)`: `Γ(g, z) = (s|𝐔(g))⁻¹(z)` and `f(g)(z) = t(Γ(g, z)) = g ∗ z`. -/
theorem corollary_7_1_17_4 {Y : Finset Obj} {V : Set Obj} (N : X.NaturalRepFinite Y V)
    {x : Obj} (hx : x ∈ Y) :
    ∃ R : X.NaturalRep x, R.U = N.U x ∧ ∀ g : X.Isotropy x, ∀ z ∈ N.U x,
      R.Γ g z = N.srcInv g.val z ∧ N.F g.val z = X.tgt (R.Γ g z) ∧
        X.tgt (R.Γ g z) = R.Φ g z := by
  obtain ⟨R, hRU, -⟩ := N.natural x hx
  refine ⟨R, hRU, fun g z hz => ?_⟩
  have hg : g.val ∈ X.morOn (Y : Set Obj) :=
    ⟨by rw [g.src_val]; exact hx, by rw [g.tgt_val]; exact hx⟩
  have hzR : z ∈ R.U := hRU ▸ hz
  have hsub : R.Γ g '' R.U ⊆ X.morOn (⋃ y ∈ Y, N.U y) := by
    rintro _ ⟨w, hw, rfl⟩
    have h := R.Γ_mem_morOn g hw
    rw [hRU] at h
    exact ⟨mem_biUnion hx h.1, mem_biUnion hx h.2⟩
  have hcc := (R.isConnected_U.image _ (R.isScSmoothOn_Γ g).continuousOn).isPreconnected
    |>.subset_connectedComponentIn ⟨x, R.mem_U, R.Γ_self g⟩ hsub
  rw [NatRepFinite.connectedComponentIn_morOn N hg (N.mem_sheet _ hg)] at hcc
  have hΓmem : R.Γ g z ∈ N.sheet g.val := hcc ⟨z, hzR, rfl⟩
  have e1 : R.Γ g z = N.srcInv g.val z := by
    have h1 := (N.isScDiffeoOn_src _ hg).left_inv _ hΓmem
    rw [R.src_Γ g z hzR] at h1
    exact h1.symm
  refine ⟨e1, ?_, R.tgt_Γ g z hzR⟩
  rw [e1]
  exact N.F_eq _ hg z (by rw [g.src_val]; exact hz)

/-- **2021 Corollary 7.1.17 (5)**, p. 301 (new in the 2021 edition): for `φ ∈ 𝐘`, `f(φ)` is
equivariant for `γ_φ(g) = φ ∘ g ∘ φ⁻¹ : G_{s(φ)} → G_{t(φ)}` (`conjIsotropy`), with the actions
`z ↦ f(g)(z)` (the natural actions, by (4)). -/
theorem corollary_7_1_17_5 {Y : Finset Obj} {V : Set Obj} (N : X.NaturalRepFinite Y V)
    {φ : Mor} (hφ : φ ∈ X.morOn (Y : Set Obj)) (g : X.Isotropy (X.src φ)) {z : Obj}
    (hz : z ∈ N.U (X.src φ)) :
    N.F φ (N.F g.val z) = N.F (X.conjIsotropy φ g).val (N.F φ z) := by
  have hg : g.val ∈ X.morOn (Y : Set Obj) :=
    ⟨by rw [g.src_val]; exact hφ.1, by rw [g.tgt_val]; exact hφ.1⟩
  set c := X.conjIsotropy φ g with hcdef
  have hc : c.val ∈ X.morOn (Y : Set Obj) :=
    ⟨by rw [c.src_val]; exact hφ.2, by rw [c.tgt_val]; exact hφ.2⟩
  have h1 := N.F_comp φ hφ g.val hg g.tgt_val.symm z (by rw [g.src_val]; exact hz)
  have h2 := N.F_comp c.val hc φ hφ c.src_val z hz
  have hcomp : X.comp c.val φ = X.comp φ g.val := by
    rw [hcdef, conjIsotropy_val]
    have e0 : X.src φ = X.tgt g.val := g.tgt_val.symm
    have e1 : X.src (X.comp φ g.val) = X.tgt (X.inv φ) := by
      rw [X.src_comp _ _ e0, g.src_val, X.tgt_inv]
    rw [X.comp_assoc _ _ _ e1 (X.src_inv φ), X.inv_comp,
      GroupoidStr.comp_unit_of_eq (by rw [X.src_comp _ _ e0, g.src_val])]
  rw [← h1, ← h2, hcomp]

/-- **2021 Corollary 7.1.17 (6)**, p. 301 (new in the 2021 edition): for `φ, ψ ∈ 𝐘` with
`s(ψ) = t(φ)`, the multiplication `(ψ', φ') ↦ ψ' ∘ φ'` is an sc-diffeomorphism from
`𝐔(ψ) ₛ×ₜ 𝐔(φ)` (an open subset of the fibred product sub-M-polyfold `𝐗 ₛ×ₜ 𝐗 ⊆ 𝐗 × 𝐗`) onto
`𝐔(ψ ∘ φ)`. -/
theorem corollary_7_1_17_6 {Y : Finset Obj} {V : Set Obj} (N : X.NaturalRepFinite Y V)
    {φ ψ : Mor} (hφ : φ ∈ X.morOn (Y : Set Obj)) (hψ : ψ ∈ X.morOn (Y : Set Obj))
    (h : X.src ψ = X.tgt φ) :
    letI := MPolyfold.paracompactSpace_prod X.PMor X.PMor
    letI := (X.PMor.prod X.PMor).paracompactSpace_subtype (MPolyfold.fibredProduct X.src X.tgt)
    ∃ m' : Mor → MPolyfold.fibredProduct X.src X.tgt,
      (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src
        X.isScSmoothMap_tgt)).IsScDiffeoOn X.PMor (fun a => X.comp a.1.1 a.1.2) m'
        {a | a.1.1 ∈ N.sheet ψ ∧ a.1.2 ∈ N.sheet φ} (N.sheet (X.comp ψ φ)) := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor X.PMor
  let _ := (X.PMor.prod X.PMor).paracompactSpace_subtype (MPolyfold.fibredProduct X.src X.tgt)
  set hA := MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src X.isScSmoothMap_tgt
  set D : Set (MPolyfold.fibredProduct X.src X.tgt) :=
    {a | a.1.1 ∈ N.sheet ψ ∧ a.1.2 ∈ N.sheet φ} with hDdef
  have hψφ : X.comp ψ φ ∈ X.morOn (Y : Set Obj) :=
    ⟨by rw [X.src_comp _ _ h]; exact hφ.1, by rw [X.tgt_comp _ _ h]; exact hψ.2⟩
  have hsψ := N.isScDiffeoOn_src ψ hψ
  have hsφ := N.isScDiffeoOn_src φ hφ
  obtain ⟨τφ, htφ⟩ := N.isScDiffeoOn_tgt φ hφ
  obtain ⟨τψ, htψ⟩ := N.isScDiffeoOn_tgt ψ hψ
  have hsψφ := N.isScDiffeoOn_src _ hψφ
  rw [X.src_comp _ _ h] at hsψφ
  let a₀ : MPolyfold.fibredProduct X.src X.tgt := ⟨(ψ, φ), h⟩
  have ha₀ : a₀ ∈ D := ⟨N.mem_sheet ψ hψ, N.mem_sheet φ hφ⟩
  -- `π₂` near `a₀`, then restricted to `D`
  obtain ⟨ι, hP⟩ : ∃ ι, (MPolyfold.subPolyfold hA).IsScDiffeoOn X.PMor
      (fun a : MPolyfold.fibredProduct X.src X.tgt => a.1.2) ι
      (Subtype.val ⁻¹' (N.sheet ψ ×ˢ (X.tgt ⁻¹' N.U (X.src ψ)))) (X.tgt ⁻¹' N.U (X.src ψ)) :=
    ⟨_, MPolyfold.isScDiffeoOn_snd_fibredProduct hA hsψ X.isScSmoothMap_tgt a₀⟩
  have hDo : IsOpen D :=
    ((N.isOpen_sheet ψ hψ).prod (N.isOpen_sheet φ hφ)).preimage continuous_subtype_val
  have hDsub : D ⊆ Subtype.val ⁻¹' (N.sheet ψ ×ˢ (X.tgt ⁻¹' N.U (X.src ψ))) := fun a ha => by
    refine ⟨ha.1, ?_⟩
    change X.tgt a.1.2 ∈ N.U (X.src ψ)
    rw [← show X.src a.1.1 = X.tgt a.1.2 from a.2]
    exact hsψ.mapsTo ha.1
  have hP' := hP.restrict hDo hDsub
  have hT : X.tgt ⁻¹' N.U (X.src ψ) ∩ ι ⁻¹' D = N.sheet φ := by
    ext y
    constructor
    · rintro ⟨hy, hyD⟩
      have := hyD.2
      rwa [hP.right_inv y hy] at this
    · intro hy
      have hy' : y ∈ X.tgt ⁻¹' N.U (X.src ψ) := by
        change X.tgt y ∈ N.U (X.src ψ)
        rw [h]
        exact htφ.mapsTo hy
      refine ⟨hy', (hP.mapsTo_inv hy').1, ?_⟩
      rw [hP.right_inv y hy']
      exact hy
  rw [hT] at hP'
  -- `D → 𝐔(φ) → U(s(φ)) → 𝐔(ψ ∘ φ)`
  have he := hsφ.comp hP'
  have hR := hsψφ.symm.comp he
  -- the multiplication maps `D` into `𝐔(ψ ∘ φ)`
  have hm : Continuous fun a : MPolyfold.fibredProduct X.src X.tgt => X.comp a.1.1 a.1.2 := by
    have h' : (MPolyfold.subPolyfold hA).IsScSmoothMap X.PMor
        fun a : MPolyfold.fibredProduct X.src X.tgt => X.comp a.1.1 a.1.2 := X.isScSmoothComp
    exact continuousOn_univ.1 h'.continuousOn
  have hDc : IsConnected D := by
    rw [← he.symm.image_eq]
    exact (N.isConnected_U _ hφ.1).image _ he.isScSmoothOn_inv.continuousOn
  have hsub : (fun a : MPolyfold.fibredProduct X.src X.tgt => X.comp a.1.1 a.1.2) '' D ⊆
      X.morOn (⋃ y ∈ Y, N.U y) := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : X.src a.1.1 = X.tgt a.1.2 := a.2
    refine ⟨?_, ?_⟩
    · rw [X.src_comp _ _ ha']
      exact mem_biUnion hφ.1 (hsφ.mapsTo ha.2)
    · rw [X.tgt_comp _ _ ha']
      exact mem_biUnion hψ.2 (htψ.mapsTo ha.1)
  have hcc := (hDc.image _ hm.continuousOn).isPreconnected.subset_connectedComponentIn
    ⟨a₀, ha₀, rfl⟩ hsub
  rw [NatRepFinite.connectedComponentIn_morOn N hψφ (N.mem_sheet _ hψφ)] at hcc
  refine ⟨_, isScDiffeoOn_congr_left_b21 hR fun a ha => ?_⟩
  have ha' : X.src a.1.1 = X.tgt a.1.2 := a.2
  have hma : X.comp a.1.1 a.1.2 ∈ N.sheet (X.comp ψ φ) := hcc ⟨a, ha, rfl⟩
  have h1 := (N.isScDiffeoOn_src _ hψφ).left_inv _ hma
  rw [X.src_comp _ _ ha'] at h1
  exact h1

variable (X) in
/-- **2021 Corollary 7.1.17 (7)**, p. 301 (new in the 2021 edition): the `U(y)` of Proposition
7.1.15 may be taken with the properness property (Definition 7.5.8; 2017: Definition 7.17). -/
theorem corollary_7_1_17_7 (Y : Finset Obj)
    (hY : ∀ y ∈ Y, ∀ y' ∈ Y, X.Isomorphic y y') {V : Set Obj} (hV : V ∈ 𝓝ˢ (Y : Set Obj)) :
    ∃ N : X.NaturalRepFinite Y V, ∀ y ∈ Y, X.HasPropernessProperty (N.U y) := by
  obtain ⟨O, hO, hOdisj⟩ := Y.finite_toSet.t2_separation
  choose P hP using fun y => X.exists_hasPropernessProperty y
  obtain ⟨W, hWo, hYW, hWV⟩ := mem_nhdsSet_iff_exists.1 hV
  have hQo : ∀ y, IsOpen (O y ∩ P y) := fun y => (hO y).2.inter (hP y).2.1
  have hV'o : IsOpen (W ∩ ⋃ y ∈ Y, (O y ∩ P y)) :=
    hWo.inter (isOpen_biUnion fun y _ => hQo y)
  have hYV' : (Y : Set Obj) ⊆ W ∩ ⋃ y ∈ Y, (O y ∩ P y) := fun y hy =>
    ⟨hYW hy, mem_biUnion hy ⟨(hO y).1, (hP y).1⟩⟩
  obtain ⟨N⟩ := X.proposition_7_1_15_2017 Y hY hV'o hYV'
  refine ⟨NatRepFinite.mono N (inter_subset_left.trans hWV), fun y hy => ?_⟩
  have hsub : N.U y ⊆ O y ∩ P y := by
    refine (N.isConnected_U y hy).isPreconnected.subset_left_of_subset_union (hQo y)
      (isOpen_biUnion (s := {y' | y' ∈ Y ∧ y' ≠ y}) fun y' _ => hQo y')
      (disjoint_iUnion₂_right.2 fun y' hy' =>
        (hOdisj hy hy'.1 (Ne.symm hy'.2)).mono inter_subset_left inter_subset_left)
      (fun z hz => ?_) ⟨y, N.mem_U y hy, (hO y).1, (hP y).1⟩
    obtain ⟨y', hy', hz'⟩ := mem_iUnion₂.1 (N.U_subset y hy hz).2
    by_cases hyy : y' = y
    · exact Or.inl (hyy ▸ hz')
    · exact Or.inr (mem_iUnion₂.2 ⟨y', ⟨hy', hyy⟩, hz'⟩)
  exact (hP y).2.mono (N.isOpen_U y hy) (hsub.trans inter_subset_right)

end EpGroupoid

end Polyfold
