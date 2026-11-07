import Polyfold.Chapter7.EpGroupoid
import Polyfold.Chapter7.LocConnected
import Polyfold.Chapter7.Discrete
import Polyfold.Chapter7.LocalDiffeo
import Polyfold.Chapter3.RestrictOpen

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §7.1,
pp. 231–233: the consequences of **Theorem 7.1** (natural representation, p. 231) which the text
discusses informally after it (the morphisms `𝐔(x)` of `U(x)` and their sheets `𝐔(g)`, the
translation groupoid `G_x ⋉ U(x)` and the claim that it is an ep-groupoid, the functor
`Γ : G_x ⋉ U(x) → X`, full and faithful, and the action `Φ̂` of `G_x` on `𝐔(x)`), and the
uniqueness of the natural representation on connected neighbourhoods, used tacitly for `T_x`
(Definition 7.12, p. 241) and in Lemma 7.3 (p. 239).  Everything is derived from the data
`NaturalRep` (`EpGroupoid.lean`); the existence, Theorem 7.1 (= Theorem 7.5, p. 253), is
`NaturalRep.lean`.  There is no 2014 preprint of Part II; numbers and pages are the 2017 text's.

# Consequences of the natural representation

## The text, paraphrased

(Theorem 7.1) For `x` with isotropy `G = G_x` and an open `V ∋ x` there are an open `U ⊆ V` of
`x`, a homomorphism `Φ : G → Diff_sc(U)` and an sc-smooth `Γ : G × U → 𝐗` with (1) `Γ(g, x) = g`,
(2) `s(Γ(g, y)) = y`, `t(Γ(g, y)) = Φ(g)(y)`, (3) every `h : y → z` between points of `U` is
`Γ(g, y)` for a unique `g`: `Γ : G × U → {φ | s(φ), t(φ) ∈ U}` is a bijection.  (p. 231) With
`𝐔(x) = {φ | s(φ), t(φ) ∈ U(x)}`, the morphism set of the full subcategory on `U(x)`, one chooses
the connected `U(x)` so small that `𝐔(x)` splits into `#G_x`-many disjoint connected components
`𝐔(g)`, `g ∈ G_x`, with `s, t : 𝐔(g) → U(x)` sc-diffeomorphisms.  (p. 232) The translation
groupoid `G_x ⋉ U(x)` has objects `U`, morphisms `G × U` ("a natural M-polyfold structure as the
finite disjoint union of copies of the M-polyfold `U`"), `s(g, y) = y`, `t(g, y) = Φ(g)(y)`,
`(g, y) ∘ (h, z) = (gh, z)`; "using the proof of Theorem 7.1 one verifies" that it is an
ep-groupoid.  The natural functor `Γ : G ⋉ U → X`, `y ↦ y`, `(g, y) ↦ Γ(g, y)`, is full and
faithful by (3), with image the full subcategory `(U(x), 𝐔(x))`.  (pp. 232–233) A morphism
`φ ∈ 𝐔(x)` lies in a unique `𝐔(h)`, `φ = Γ(h, s(φ))`, `t(φ) = Φ(h)(s(φ))`;
`Φ̂(g)(φ) = Γ(g h g⁻¹, g ∗ s(φ)) ∈ 𝐔(g h g⁻¹)` defines a homomorphism `Φ̂ : G_x → Diff_sc(𝐔(x))`
with `Φ̂(g)(𝐔(h)) = 𝐔(g h g⁻¹)`, `s ∘ Φ̂(g) = Φ(g) ∘ s` and `t ∘ Φ̂(g) = Φ(g) ∘ t`.

## What is formalized (namespace `Polyfold.EpGroupoid.NaturalRep`, `R : X.NaturalRep x`)

* **The sheets** `𝐔(g) = Γ(g, U)`: `isOpen_image_Γ` (the image of a continuous section of the
  local homeomorphism `s`), `isConnected_image_Γ`, `pairwise_disjoint_image_Γ`, `iUnion_image_Γ`
  (`⋃_g 𝐔(g) = 𝐔(x)`, i.e. `X.morOn R.U`), `isOpen_morOn`, `connectedComponentIn_morOn` (the
  `𝐔(g)` are the connected components of `𝐔(x)`), `injective_image_Γ` (there are `#G_x` of them),
  `isScDiffeoOn_src_image`, `isScDiffeoOn_tgt_image` (`s, t : 𝐔(g) → U` are sc-diffeomorphisms),
  `Γ_inj`, `bijOn_Γ` (**Theorem 7.1 (3)** as a bijection `G_x × U → 𝐔(x)`).
* **The sheet index** `index φ` (`φ ∈ 𝐔(index φ)`): `Γ_index` (`φ = Γ(h, s φ)`),
  `tgt_eq_Φ_index` (`t φ = Φ(h)(s φ)`), `index_Γ`, `index_eq_iff`, `eventually_index_eq` (locally
  constant on `𝐔(x)`).
* **`Γ` is a functor `G_x ⋉ U → X`**: `Γ_mul` (`Γ(g, Φ(h) y) ∘ Γ(h, y) = Γ(gh, y)`), `Γ_one`
  (`Γ(1, y) = 1_y`), `Γ_inv` (`Γ(g⁻¹, Φ(g) y) = Γ(g, y)⁻¹`); `functor : GroupoidFunctor
  R.translationGroupoid X.toGroupoidStr`, the inclusion on objects (`functor_obj`, `functor_mor`);
  **full and faithful** through the bridge: the instances `full : R.functor.toFunctor.Full` and
  `faithful : R.functor.toFunctor.Faithful`.
* **Uniqueness**: for natural representations `R, R'` at `x` and the connected component
  `C = connectedComponentIn (R.U ∩ R'.U) x` (open and connected:
  `isOpen_connectedComponentIn_inter`, `isConnected_connectedComponentIn_inter`): `Γ_eqOn`
  (`R.Γ g = R'.Γ g` on `C`), `Φ_eqOn` (`R.Φ g = R'.Φ g` on `C`), `mapsTo_Φ_connectedComponentIn`
  (`C` is invariant);
  `eventually_Φ_eq_of_actsTrivially` (if `g` acts trivially for one natural representation, then
  `Φ(g) = id` near `x` for every one); `restrict` (to an invariant open connected `W ⊆ U`),
  `restrictInter` (to `C`) and `restrictInter_eq` (the restrictions of `R` and `R'` agree).
* **`Φ̂`**: `Φhat g φ = Γ(g, t φ) ∘ φ ∘ Γ(g, s φ)⁻¹`; `Φhat_Γ` (the text's formula),
  `Φhat_mem_image`, `image_Φhat` (`Φ̂(g)(𝐔(h)) = 𝐔(g h g⁻¹)`), `index_Φhat`, `src_Φhat` and
  `tgt_Φhat` (the two commutative diagrams), `Φ_conj`, `mapsTo_Φhat`, `Φhat_one`, `Φhat_mul` (a
  homomorphism), `isScSmoothOn_Φhat`, `isScDiffeoOn_Φhat` (`Φ̂(g) ∈ Diff_sc(𝐔(x))`, with inverse
  `Φ̂(g⁻¹)`).
* **`G_x ⋉ U(x)` is an ep-groupoid**: `translationEpGroupoid : EpGroupoid R.U (X.Isotropy x × R.U)`,
  objects `objPolyfold` (the open subset `U`, Part I's `MPolyfold.restrictOpen`), morphisms
  `morPolyfold` (`discretePolyfold G_x` times `U`, `MPolyfold.prod`); the conditions of Definition
  7.3 as `translation_isLocalScDiffeo_src`, `translation_isLocalScDiffeo_tgt`,
  `translation_isProperMap` (for every `V`), `translation_isScSmoothCompSheet`, with
  `isScSmoothMap_smul` and `shearHomeomorph` (`(g, y) ↦ (g, g ∗ y)`).  `epFunctor :
  EpFunctor R.translationEpGroupoid X`: `Γ` is a morphism of `EP` (Definition 7.7).  The scoped
  instances (`open scoped Polyfold.EpGroupoid.NaturalRep`) are the discrete topology of `G_x`,
  `Nonempty U` and the paracompactness of `U` and of `G_x × U`.

## Reading

* **Connectedness of `U` makes `Γ` a functor** (PLAN II.6, 3).  `y ↦ Γ(g, Φ(h) y) ∘ Γ(h, y)` and
  `Γ(gh, ·)` are continuous sections of `s` over `U` (the first by condition (4) in the sheet form,
  for the sheet `𝐔(g)`) with the same value `g ∘ h` at `x`; on the connected `U` they agree
  (`eqOn_sections_of_isPreconnected`, `LocConnected.lean`).  Equivalently, the sheet index of
  `Γ(g, Φ(h) y) ∘ Γ(h, y)` is locally constant (`eventually_index_eq`), hence constant.
  `Γ_inv` then follows from the uniqueness of inverses.
* **The sheets.**  Once the data of Theorem 7.1 are given with `U` connected, the text's "choose
  `U(x)` so small that `𝐔(x)` splits into `#G_x`-many connected components" needs no further
  shrinking: the `𝐔(g) = Γ(g, U)` are open, connected, disjoint, nonempty and cover `𝐔(x)`.  "`𝐔(x)`
  fits into an arbitrarily small open neighbourhood of `G_x`" belongs to the construction of
  Theorem 7.1 (`NaturalRep.lean`) and is not formalized here.
* **Uniqueness** holds on the connected component of `x` in `U ∩ U'`, which is open, connected and
  invariant; `U ∩ U'` itself need not be connected.  This is the form that `T_x` (Definition 7.12)
  and Lemma 7.3 need (`eventually_Φ_eq_of_actsTrivially`).
* **`Φ̂`** is defined as the conjugation `Γ(g, t φ) ∘ φ ∘ Γ(g, s φ)⁻¹`, a total map; the text's
  definition `Φ̂(g)(φ) = Γ(g h g⁻¹, g ∗ s(φ))` for `φ ∈ 𝐔(h)` is `Φhat_Γ`.  "`Φ̂ : G_x →
  Diff_sc(𝐔(x))` is a group homomorphism" is read as `Φhat_one`, `Φhat_mul` on `𝐔(x)` and
  `isScDiffeoOn_Φhat`, in the style of `NaturalRep`'s `Φ`.
* **`G_x ⋉ U(x)` as an ep-groupoid.**  "The finite group `G`" carries the discrete topology and
  `G × U` the product of `discretePolyfold G` with the open-subset M-polyfold `U` (`Discrete.lean`:
  "the finite disjoint union of copies of `U`").  The text's "using the proof of Theorem 7.1" is not
  needed: the conditions follow from the data alone.  Properness holds for every `V(y)` (here `U`):
  `t = π₂ ∘ ((g, y) ↦ (g, g ∗ y))` with `G_x` finite.  The finiteness (Proposition 7.4) is
  re-derived privately (`finite_isotropy`, from `Discrete.lean`) so that this file does not import
  `Basic.lean`.  Condition (4) is checked in the sheet form: `σ(t ψ) ∘ ψ = (k(ψ) ψ₁, ψ₂)` with a
  locally constant `k`.
* "Full" and "faithful" are Mathlib's `Functor.Full`, `Functor.Faithful` of
  `GroupoidFunctor.toFunctor` (the bridge `GroupoidStr.Ob`), as in Definition 7.9's
  `LocalUniformizer`.
* No hypothesis "for all …" is added: everything is a consequence of one datum `R`, and such data
  exist (`EpGroupoid.trivialNaturalRep`; in general Theorem 7.1).
* No possible misprint was found on pp. 231–233.
-/

open Set Filter Topology Function CategoryTheory

noncomputable section

namespace Polyfold

/-- A continuous section `σ` of a continuous locally injective map `p` over an open set `U` has
open image. -/
private theorem isOpen_image_of_section {M Y : Type*} [TopologicalSpace M] [TopologicalSpace Y]
    {p : M → Y} (hp : IsLocallyInjective p) (hpc : Continuous p) {U : Set Y} (hU : IsOpen U)
    {σ : Y → M} (hσ : ContinuousOn σ U) (hsec : ∀ y ∈ U, p (σ y) = y) : IsOpen (σ '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨W, hWo, hyW, hinj⟩ := hp (σ y)
  have hN : IsOpen (U ∩ σ ⁻¹' W) := hσ.isOpen_inter_preimage hU hWo
  refine ⟨W ∩ p ⁻¹' (U ∩ σ ⁻¹' W), fun ψ hψ => ?_, hWo.inter (hN.preimage hpc), hyW, ?_⟩
  · exact ⟨p ψ, hψ.2.1, hinj hψ.2.2 hψ.1 (hsec _ hψ.2.1)⟩
  · change p (σ y) ∈ U ∩ σ ⁻¹' W
    rw [hsec y hy]
    exact ⟨hy, hyW⟩

/-- The inclusion of an open subset is sc-smooth. -/
private theorem isScSmoothMap_restrictOpen_val {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] (PY : MPolyfold Y) {V : Set Y} [Nonempty V] [ParacompactSpace V]
    (hV : IsOpen V) : (PY.restrictOpen hV).IsScSmoothMap PY (Subtype.val : V → Y) := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ continuous_subtype_val.continuousOn
    fun v _ => ?_
  obtain ⟨φ, hφ, hv⟩ := PY.exists_isChart_mem_source v.1
  set φ' := φ.restrict (s := φ.source ∩ V) inter_subset_left (φ.isOpen_source.inter hV)
  have hφ'c : PY.IsChart φ' := MPolyfold.IsChart.restrict PY hφ _ _
  have hsub : φ'.source ⊆ V := inter_subset_right
  refine ⟨φ'.restrictTo hsub, φ', Subtype.val ⁻¹' φ'.source,
    MPolyfold.isChart_restrictTo hV hφ'c hsub, hφ'c,
    φ'.isOpen_source.preimage continuous_subtype_val, ⟨hv, v.2⟩, fun w hw => ⟨mem_univ _, hw⟩,
    fun w hw => hw, ?_⟩
  rw [show Subtype.val ⁻¹' φ'.source = (φ'.restrictTo hsub).source from rfl,
    (φ'.restrictTo hsub).image_source]
  refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
  change z = φ' ((φ'.restrictTo hsub).symm z).1
  rw [MChart.restrictTo_symm_val hsub hz, φ'.apply_symm_apply hz]

/-- A continuous map into a discrete M-polyfold is sc-smooth on an open set. -/
private theorem isScSmoothOn_discrete_of_continuousOn {G : Type*} [TopologicalSpace G]
    [DiscreteTopology G] {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {PY : MPolyfold Y} {f : Y → G} {W : Set Y} (hW : IsOpen W) (hf : ContinuousOn f W) :
    PY.IsScSmoothOn (discretePolyfold G) f W := by
  refine MPolyfold.IsScSmoothOn.of_locally hW fun y hy => ⟨W ∩ f ⁻¹' {f y},
    hf.isOpen_inter_preimage hW (isOpen_discrete _), ⟨hy, rfl⟩, inter_subset_left, ?_⟩
  exact ((isScSmoothMap_const_discrete (f y)).mono
    (hf.isOpen_inter_preimage hW (isOpen_discrete _)) (subset_univ _)).congr
    fun z hz => hz.2.symm

namespace EpGroupoid

namespace NaturalRep

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}
  (R : X.NaturalRep x)

/-! ### The sheets `𝐔(g) = Γ(g, U)` -/

theorem continuousOn_Γ (g : X.Isotropy x) : ContinuousOn (R.Γ g) R.U :=
  (R.isScSmoothOn_Γ g).continuousOn

theorem continuousOn_Φ (g : X.Isotropy x) : ContinuousOn (R.Φ g) R.U :=
  (R.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn

/-- `Φ(g⁻¹)(Φ(g)(y)) = y`. -/
theorem Φ_inv_Φ (g : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) : R.Φ g⁻¹ (R.Φ g y) = y :=
  (R.isScDiffeoOn_Φ g).left_inv y hy

/-- `Φ(g)(Φ(g⁻¹)(y)) = y`. -/
theorem Φ_Φ_inv (g : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) : R.Φ g (R.Φ g⁻¹ y) = y :=
  (R.isScDiffeoOn_Φ g).right_inv y hy

/-- **The sheet `𝐔(g) = Γ(g, U)` is open**: it is the image of a continuous section of the local
homeomorphism `s` over the open `U`. -/
theorem isOpen_image_Γ (g : X.Isotropy x) : IsOpen (R.Γ g '' R.U) :=
  isOpen_image_of_section X.isLocalScDiffeo_src.isLocallyInjective X.continuous_src R.isOpen_U
    (R.continuousOn_Γ g) (R.src_Γ g)

theorem Γ_mem_image (g : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) : R.Γ g y ∈ R.Γ g '' R.U :=
  mem_image_of_mem _ hy

/-- On the sheet `𝐔(g)`, `Γ(g, s φ) = φ`. -/
theorem Γ_src_of_mem_image {g : X.Isotropy x} {φ : Mor} (hφ : φ ∈ R.Γ g '' R.U) :
    R.Γ g (X.src φ) = φ := by
  obtain ⟨y, hy, rfl⟩ := hφ
  rw [R.src_Γ g y hy]

theorem src_mem_of_mem_image {g : X.Isotropy x} {φ : Mor} (hφ : φ ∈ R.Γ g '' R.U) :
    X.src φ ∈ R.U := by
  obtain ⟨y, hy, rfl⟩ := hφ
  rw [R.src_Γ g y hy]
  exact hy

/-- **`s : 𝐔(g) → U` is an sc-diffeomorphism**, with inverse `Γ(g, ·)` (p. 231). -/
theorem isScDiffeoOn_src_image (g : X.Isotropy x) :
    X.PMor.IsScDiffeoOn X.PObj X.src (R.Γ g) (R.Γ g '' R.U) R.U where
  isScSmoothOn := X.isScSmoothMap_src.mono (R.isOpen_image_Γ g) (subset_univ _)
  isScSmoothOn_inv := R.isScSmoothOn_Γ g
  mapsTo _ hφ := R.src_mem_of_mem_image hφ
  mapsTo_inv _ hy := R.Γ_mem_image g hy
  left_inv _ hφ := R.Γ_src_of_mem_image hφ
  right_inv y hy := R.src_Γ g y hy

/-- **`t : 𝐔(g) → U` is an sc-diffeomorphism**, with inverse `z ↦ Γ(g, Φ(g⁻¹)(z))` (p. 231). -/
theorem isScDiffeoOn_tgt_image (g : X.Isotropy x) :
    X.PMor.IsScDiffeoOn X.PObj X.tgt (fun z => R.Γ g (R.Φ g⁻¹ z)) (R.Γ g '' R.U) R.U where
  isScSmoothOn := X.isScSmoothMap_tgt.mono (R.isOpen_image_Γ g) (subset_univ _)
  isScSmoothOn_inv := MPolyfold.IsScSmoothOn.comp (R.isScSmoothOn_Γ g)
    (R.isScDiffeoOn_Φ g).isScSmoothOn_inv (R.isScDiffeoOn_Φ g).mapsTo_inv
  mapsTo := by
    rintro _ ⟨y, hy, rfl⟩
    rw [R.tgt_Γ g y hy]
    exact R.mapsTo_Φ g hy
  mapsTo_inv _ hz := R.Γ_mem_image g ((R.isScDiffeoOn_Φ g).mapsTo_inv hz)
  left_inv := by
    rintro _ ⟨y, hy, rfl⟩
    rw [R.tgt_Γ g y hy, R.Φ_inv_Φ g hy]
  right_inv z hz := by
    rw [R.tgt_Γ g _ ((R.isScDiffeoOn_Φ g).mapsTo_inv hz), R.Φ_Φ_inv g hz]

/-- `Γ(g, y) = Γ(h, y)` only for `g = h` (Theorem 7.1 (3)). -/
theorem Γ_inj {g h : X.Isotropy x} {y : Obj} (hy : y ∈ R.U) : R.Γ g y = R.Γ h y ↔ g = h := by
  refine ⟨fun he => ?_, fun he => he ▸ rfl⟩
  have hs : X.src (R.Γ g y) = y := R.src_Γ g y hy
  obtain ⟨k, -, hk⟩ := R.existsUnique_Γ (R.Γ g y) (by rw [hs]; exact hy)
    (by rw [R.tgt_Γ g y hy]; exact R.mapsTo_Φ g hy)
  rw [hs] at hk
  exact (hk g rfl).trans (hk h he.symm).symm

/-- **The sheets are pairwise disjoint** (p. 231: `𝐔(x) = ⊔_g 𝐔(g)`). -/
theorem pairwise_disjoint_image_Γ :
    Pairwise (Disjoint on fun g : X.Isotropy x => R.Γ g '' R.U) := by
  intro g h hgh
  refine disjoint_left.2 ?_
  rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', he⟩
  have hyy' : y' = y := by rw [← R.src_Γ h y' hy', he, R.src_Γ g y hy]
  subst hyy'
  exact hgh ((R.Γ_inj hy).1 he.symm)

/-- **The sheets cover the morphisms of `U`**: `⋃_g 𝐔(g) = 𝐔(x) = {φ | s φ, t φ ∈ U}`. -/
theorem iUnion_image_Γ : ⋃ g : X.Isotropy x, R.Γ g '' R.U = X.morOn R.U := by
  refine Subset.antisymm (iUnion_subset fun g => ?_) fun φ hφ => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact R.Γ_mem_morOn g hy
  · obtain ⟨g, hg, -⟩ := R.existsUnique_Γ φ hφ.1 hφ.2
    exact mem_iUnion.2 ⟨g, X.src φ, hφ.1, hg⟩

/-- `𝐔(x)` is open. -/
theorem isOpen_morOn : IsOpen (X.morOn R.U) := by
  rw [← R.iUnion_image_Γ]
  exact isOpen_iUnion R.isOpen_image_Γ

/-- The sheet `𝐔(g)` is connected (the image of the connected `U`). -/
theorem isConnected_image_Γ (g : X.Isotropy x) : IsConnected (R.Γ g '' R.U) :=
  R.isConnected_U.image _ (R.continuousOn_Γ g)

/-- **The sheets are the connected components of `𝐔(x)`** (p. 231: "`𝐔(x)` splits into
`#G_x`-many (disjoint) connected components enumerated by the group elements"). -/
theorem connectedComponentIn_morOn {g : X.Isotropy x} {φ : Mor} (hφ : φ ∈ R.Γ g '' R.U) :
    connectedComponentIn (X.morOn R.U) φ = R.Γ g '' R.U := by
  have hsub : R.Γ g '' R.U ⊆ X.morOn R.U := by
    rw [← R.iUnion_image_Γ]
    exact subset_iUnion (fun h => R.Γ h '' R.U) g
  refine Subset.antisymm ?_
    ((R.isConnected_image_Γ g).isPreconnected.subset_connectedComponentIn hφ hsub)
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union (R.isOpen_image_Γ g)
    (v := ⋃ h ∈ {h | h ≠ g}, R.Γ h '' R.U) (isOpen_biUnion fun h _ => R.isOpen_image_Γ h)
    (disjoint_iUnion₂_right.2 fun h hh => R.pairwise_disjoint_image_Γ (Ne.symm hh))
    (fun ψ hψ => ?_) ⟨φ, mem_connectedComponentIn (hsub hφ), hφ⟩
  have hψ' := connectedComponentIn_subset _ _ hψ
  rw [← R.iUnion_image_Γ] at hψ'
  obtain ⟨k, hk⟩ := mem_iUnion.1 hψ'
  by_cases hkg : k = g
  · exact Or.inl (hkg ▸ hk)
  · exact Or.inr (mem_iUnion₂.2 ⟨k, hkg, hk⟩)

/-- The sheets are nonempty, so there are `#G_x` of them: `g ↦ 𝐔(g)` is injective. -/
theorem injective_image_Γ : Function.Injective fun g : X.Isotropy x => R.Γ g '' R.U := by
  intro g h hgh
  by_contra hne
  have hd : Disjoint (R.Γ g '' R.U) (R.Γ h '' R.U) := R.pairwise_disjoint_image_Γ hne
  have hgh' : R.Γ g '' R.U = R.Γ h '' R.U := hgh
  rw [hgh', disjoint_self, bot_eq_empty, image_eq_empty] at hd
  exact (hd ▸ R.mem_U : x ∈ (∅ : Set Obj))

/-- **Theorem 7.1 (3)**: `Γ : G_x × U → 𝐔(x)` is a bijection. -/
theorem bijOn_Γ :
    BijOn (fun p : X.Isotropy x × Obj => R.Γ p.1 p.2) (univ ×ˢ R.U) (X.morOn R.U) := by
  refine ⟨fun p hp => R.Γ_mem_morOn p.1 hp.2, fun p hp q hq he => ?_, fun φ hφ => ?_⟩
  · have h2 : p.2 = q.2 := by
      have := congrArg X.src he
      simp only [R.src_Γ _ _ hp.2, R.src_Γ _ _ hq.2] at this
      exact this
    have h1 : p.1 = q.1 := by
      simp only [h2] at he
      exact (R.Γ_inj hq.2).1 he
    exact Prod.ext h1 h2
  · obtain ⟨g, hg, -⟩ := R.existsUnique_Γ φ hφ.1 hφ.2
    exact ⟨(g, X.src φ), ⟨mem_univ _, hφ.1⟩, hg⟩

/-- Every morphism of `𝐔(x)` is `Γ(h, s φ)` for some `h`. -/
theorem exists_Γ_eq {φ : Mor} (hφ : φ ∈ X.morOn R.U) : ∃ h, R.Γ h (X.src φ) = φ :=
  (R.existsUnique_Γ φ hφ.1 hφ.2).exists

open scoped Classical in
/-- **The sheet index** of `φ ∈ 𝐔(x)`: the unique `h ∈ G_x` with `φ ∈ 𝐔(h)` (p. 232; `1` off
`𝐔(x)`). -/
def index (φ : Mor) : X.Isotropy x :=
  if hφ : φ ∈ X.morOn R.U then (R.exists_Γ_eq hφ).choose else 1

/-- `φ = Γ(h, s φ)` for the sheet index `h` of `φ` (p. 232). -/
theorem Γ_index {φ : Mor} (hφ : φ ∈ X.morOn R.U) : R.Γ (R.index φ) (X.src φ) = φ := by
  rw [index, dif_pos hφ]
  exact (R.exists_Γ_eq hφ).choose_spec

/-- `t φ = Φ(h)(s φ)` for the sheet index `h` of `φ` (p. 232). -/
theorem tgt_eq_Φ_index {φ : Mor} (hφ : φ ∈ X.morOn R.U) :
    X.tgt φ = R.Φ (R.index φ) (X.src φ) := by
  conv_lhs => rw [← R.Γ_index hφ]
  exact R.tgt_Γ _ _ hφ.1

theorem index_Γ (g : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) : R.index (R.Γ g y) = g := by
  have h := R.Γ_index (R.Γ_mem_morOn g hy)
  rw [R.src_Γ g y hy] at h
  exact (R.Γ_inj hy).1 h

/-- The sheet index of `φ ∈ 𝐔(x)` is `g` iff `φ ∈ 𝐔(g)`. -/
theorem index_eq_iff {φ : Mor} (hφ : φ ∈ X.morOn R.U) {g : X.Isotropy x} :
    R.index φ = g ↔ φ ∈ R.Γ g '' R.U := by
  refine ⟨fun h => ⟨X.src φ, hφ.1, h ▸ R.Γ_index hφ⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩
  exact R.index_Γ g hy

/-- **The sheet index is locally constant on `𝐔(x)`** (PLAN II.6, 3): it is constant on the open
sheets. -/
theorem eventually_index_eq {φ : Mor} (hφ : φ ∈ X.morOn R.U) :
    ∀ᶠ ψ in 𝓝 φ, R.index ψ = R.index φ := by
  have hmem : φ ∈ R.Γ (R.index φ) '' R.U := (R.index_eq_iff hφ).1 rfl
  filter_upwards [(R.isOpen_image_Γ _).mem_nhds hmem] with ψ hψ
  obtain ⟨y, hy, rfl⟩ := hψ
  exact R.index_Γ _ hy

/-! ### `Γ` is a functor `G_x ⋉ U → X` -/

/-- `ψ ↦ Γ(g, t ψ) ∘ ψ` is sc-smooth on `t⁻¹(U)` (condition (4) of Definition 7.3 in the sheet
form, for the sheet `𝐔(g)`). -/
theorem isScSmoothOn_comp_Γ_tgt (g : X.Isotropy x) :
    X.PMor.IsScSmoothOn X.PMor (fun ψ => X.comp (R.Γ g (X.tgt ψ)) ψ) (X.tgt ⁻¹' R.U) :=
  X.isScSmoothCompSheet (R.Γ g) _ _ (R.isScDiffeoOn_src_image g)

/-- **`Γ` is multiplicative**: `Γ(g, Φ(h) y) ∘ Γ(h, y) = Γ(gh, y)` for `y ∈ U`.  Both sides are
continuous sections of `s` over the connected `U` which agree at `x`. -/
theorem Γ_mul (g h : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) :
    X.comp (R.Γ g (R.Φ h y)) (R.Γ h y) = R.Γ (g * h) y := by
  have hsm : X.PObj.IsScSmoothOn X.PMor (fun y => X.comp (R.Γ g (R.Φ h y)) (R.Γ h y)) R.U := by
    refine (MPolyfold.IsScSmoothOn.comp (R.isScSmoothOn_comp_Γ_tgt g) (R.isScSmoothOn_Γ h)
      fun y hy => ?_).congr fun y hy => ?_
    · change X.tgt (R.Γ h y) ∈ R.U
      rw [R.tgt_Γ h y hy]
      exact R.mapsTo_Φ h hy
    · simp only [Function.comp_apply, R.tgt_Γ h y hy]
  refine eqOn_sections_of_isPreconnected X.isLocalScDiffeo_src.isLocallyInjective
    R.isConnected_U.isPreconnected hsm.continuousOn (R.continuousOn_Γ (g * h)) (fun y hy => ?_)
    (R.src_Γ (g * h)) R.mem_U ?_ hy
  · have hc : X.src (R.Γ g (R.Φ h y)) = X.tgt (R.Γ h y) := by
      rw [R.src_Γ g _ (R.mapsTo_Φ h hy), R.tgt_Γ h y hy]
    change X.src (X.comp (R.Γ g (R.Φ h y)) (R.Γ h y)) = y
    rw [X.src_comp _ _ hc, R.src_Γ h y hy]
  · rw [R.Φ_self, R.Γ_self, R.Γ_self, R.Γ_self, GroupoidStr.Isotropy.val_mul]

/-- **`Γ` preserves units**: `Γ(1, y) = 1_y` for `y ∈ U`. -/
theorem Γ_one {y : Obj} (hy : y ∈ R.U) : R.Γ 1 y = X.unit y := by
  refine eqOn_sections_of_isPreconnected X.isLocalScDiffeo_src.isLocallyInjective
    R.isConnected_U.isPreconnected (R.continuousOn_Γ 1) X.continuous_unit.continuousOn
    (R.src_Γ 1) (fun y _ => X.src_unit y) R.mem_U ?_ hy
  rw [R.Γ_self, GroupoidStr.Isotropy.val_one]

/-- **`Γ` preserves inverses**: `Γ(g⁻¹, Φ(g) y) = Γ(g, y)⁻¹` for `y ∈ U`. -/
theorem Γ_inv (g : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) :
    R.Γ g⁻¹ (R.Φ g y) = X.inv (R.Γ g y) := by
  refine GroupoidStr.eq_inv_of_comp_eq_unit (G := X.toGroupoidStr) ?_ ?_
  · rw [R.src_Γ _ _ (R.mapsTo_Φ g hy), R.tgt_Γ g y hy]
  · rw [R.Γ_mul _ _ hy, inv_mul_cancel, R.Γ_one hy, R.src_Γ g y hy]

/-- **`Γ` as a functor** `G_x ⋉ U(x) → X` (p. 232): the inclusion `y ↦ y` on objects and
`(g, y) ↦ Γ(g, y)` on morphisms. -/
def functor : GroupoidFunctor R.translationGroupoid X.toGroupoidStr where
  obj y := (y : Obj)
  mor p := R.Γ p.1 p.2
  src_mor p := R.src_Γ p.1 p.2 p.2.2
  tgt_mor p := R.tgt_Γ p.1 p.2 p.2.2
  mor_comp p q h := by
    have h' : (p.2 : Obj) = R.Φ q.1 q.2 := congrArg Subtype.val h
    change R.Γ (p.1 * q.1) q.2 = X.comp (R.Γ p.1 p.2) (R.Γ q.1 q.2)
    rw [h', R.Γ_mul _ _ q.2.2]
  mor_unit y := R.Γ_one y.2

@[simp]
theorem functor_obj (y : R.U) : R.functor.obj y = y := rfl

@[simp]
theorem functor_mor (p : X.Isotropy x × R.U) : R.functor.mor p = R.Γ p.1 p.2 := rfl

/-- **`Γ` is full** (p. 232): every morphism `y → z` of `X` between points of `U` is `Γ(g, y)`. -/
instance full : R.functor.toFunctor.Full where
  map_surjective {y z} f := by
    let y' : R.U := y
    let z' : R.U := z
    have hy : X.src f.1 = y'.1 := f.2.1
    have hz : X.tgt f.1 = z'.1 := f.2.2
    obtain ⟨g, hg, -⟩ := R.existsUnique_Γ f.1 (by rw [hy]; exact y'.2) (by rw [hz]; exact z'.2)
    rw [hy] at hg
    refine ⟨⟨(g, y'), rfl, Subtype.ext ?_⟩, Subtype.ext hg⟩
    change R.Φ g y'.1 = z'.1
    rw [← R.tgt_Γ g y'.1 y'.2, hg, hz]

/-- **`Γ` is faithful** (p. 232): `Γ(g, y) = Γ(g', y)` only for `g = g'`. -/
instance faithful : R.functor.toFunctor.Faithful where
  map_injective {y z} {f f'} he := by
    have he' : R.Γ f.1.1 f.1.2 = R.Γ f'.1.1 f'.1.2 := congrArg Subtype.val he
    have h2 : f.1.2 = f'.1.2 := f.2.1.trans f'.2.1.symm
    rw [h2] at he'
    exact Subtype.ext (Prod.ext ((R.Γ_inj f'.1.2.2).1 he') h2)

/-! ### Uniqueness on connected neighbourhoods -/

section Uniqueness

variable (R' : X.NaturalRep x)

/-- The connected component of `x` in `U ∩ U'` is open (M-polyfolds are locally connected). -/
theorem isOpen_connectedComponentIn_inter : IsOpen (connectedComponentIn (R.U ∩ R'.U) x) :=
  X.PObj.isOpen_connectedComponentIn (R.isOpen_U.inter R'.isOpen_U) x

theorem mem_connectedComponentIn_inter : x ∈ connectedComponentIn (R.U ∩ R'.U) x :=
  mem_connectedComponentIn ⟨R.mem_U, R'.mem_U⟩

theorem isConnected_connectedComponentIn_inter :
    IsConnected (connectedComponentIn (R.U ∩ R'.U) x) :=
  ⟨⟨x, R.mem_connectedComponentIn_inter R'⟩, isPreconnected_connectedComponentIn⟩

/-- **Uniqueness of `Γ`** (used tacitly for `T_x`, Definition 7.12, and in Lemma 7.3): two
natural representations at `x` have the same `Γ(g, ·)` on the connected component of `x` in
`U ∩ U'`.  Both are continuous sections of `s` through `g`. -/
theorem Γ_eqOn (g : X.Isotropy x) :
    EqOn (R.Γ g) (R'.Γ g) (connectedComponentIn (R.U ∩ R'.U) x) := by
  have hC := connectedComponentIn_subset (R.U ∩ R'.U) x
  exact eqOn_sections_of_isPreconnected X.isLocalScDiffeo_src.isLocallyInjective
    isPreconnected_connectedComponentIn ((R.continuousOn_Γ g).mono fun y hy => (hC hy).1)
    ((R'.continuousOn_Γ g).mono fun y hy => (hC hy).2) (fun y hy => R.src_Γ g y (hC hy).1)
    (fun y hy => R'.src_Γ g y (hC hy).2) (R.mem_connectedComponentIn_inter R')
    ((R.Γ_self g).trans (R'.Γ_self g).symm)

/-- **Uniqueness of `Φ`**: two natural representations at `x` have the same `Φ(g)` on the
connected component of `x` in `U ∩ U'`. -/
theorem Φ_eqOn (g : X.Isotropy x) :
    EqOn (R.Φ g) (R'.Φ g) (connectedComponentIn (R.U ∩ R'.U) x) := fun y hy => by
  have hC := connectedComponentIn_subset (R.U ∩ R'.U) x hy
  rw [← R.tgt_Γ g y hC.1, R.Γ_eqOn R' g hy, R'.tgt_Γ g y hC.2]

/-- The connected component of `x` in `U ∩ U'` is invariant under the action. -/
theorem mapsTo_Φ_connectedComponentIn (g : X.Isotropy x) :
    MapsTo (R.Φ g) (connectedComponentIn (R.U ∩ R'.U) x) (connectedComponentIn (R.U ∩ R'.U) x) := by
  have hC := connectedComponentIn_subset (R.U ∩ R'.U) x
  have hsub : R.Φ g '' connectedComponentIn (R.U ∩ R'.U) x ⊆
      connectedComponentIn (R.U ∩ R'.U) x := by
    refine (isPreconnected_connectedComponentIn.image _
      ((R.continuousOn_Φ g).mono fun y hy => (hC hy).1)).subset_connectedComponentIn
      ⟨x, R.mem_connectedComponentIn_inter R', R.Φ_self g⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨R.mapsTo_Φ g (hC hy).1, ?_⟩
    rw [R.Φ_eqOn R' g hy]
    exact R'.mapsTo_Φ g (hC hy).2
  exact fun y hy => hsub (mem_image_of_mem _ hy)

/-- If `g` acts trivially (Definition 7.12: `Φ'(g) = id` for some natural representation `R'`),
then `Φ(g) = id` near `x` for every natural representation `R`. -/
theorem eventually_Φ_eq_of_actsTrivially {g : X.Isotropy x} (hg : X.ActsTrivially g) :
    ∀ᶠ y in 𝓝 x, R.Φ g y = y := by
  obtain ⟨R', hR'⟩ := hg
  filter_upwards [(R.isOpen_connectedComponentIn_inter R').mem_nhds
    (R.mem_connectedComponentIn_inter R')] with y hy
  rw [R.Φ_eqOn R' g hy]
  exact hR' y (connectedComponentIn_subset _ _ hy).2

end Uniqueness

/-! ### Restriction to an invariant connected neighbourhood -/

/-- **The restriction** of a natural representation to an open connected neighbourhood `W ⊆ U`
of `x` invariant under the action. -/
def restrict (W : Set Obj) (hWo : IsOpen W) (hWc : IsConnected W) (hxW : x ∈ W) (hWU : W ⊆ R.U)
    (hinv : ∀ g, MapsTo (R.Φ g) W W) : X.NaturalRep x where
  U := W
  isOpen_U := hWo
  isConnected_U := hWc
  mem_U := hxW
  Φ := R.Φ
  Γ := R.Γ
  isScDiffeoOn_Φ g :=
    { isScSmoothOn := (R.isScDiffeoOn_Φ g).isScSmoothOn.mono hWo hWU
      isScSmoothOn_inv := (R.isScDiffeoOn_Φ g).isScSmoothOn_inv.mono hWo hWU
      mapsTo := hinv g
      mapsTo_inv := hinv g⁻¹
      left_inv := fun y hy => (R.isScDiffeoOn_Φ g).left_inv y (hWU hy)
      right_inv := fun y hy => (R.isScDiffeoOn_Φ g).right_inv y (hWU hy) }
  Φ_mul g h y hy := R.Φ_mul g h y (hWU hy)
  isScSmoothOn_Γ g := (R.isScSmoothOn_Γ g).mono hWo hWU
  Γ_self := R.Γ_self
  src_Γ g y hy := R.src_Γ g y (hWU hy)
  tgt_Γ g y hy := R.tgt_Γ g y (hWU hy)
  existsUnique_Γ h hs ht := R.existsUnique_Γ h (hWU hs) (hWU ht)

@[simp]
theorem restrict_U (W : Set Obj) (hWo : IsOpen W) (hWc : IsConnected W) (hxW : x ∈ W)
    (hWU : W ⊆ R.U) (hinv : ∀ g, MapsTo (R.Φ g) W W) :
    (R.restrict W hWo hWc hxW hWU hinv).U = W := rfl

/-- The restriction of `R` to the connected component of `x` in `U ∩ U'` (open, connected and
invariant). -/
def restrictInter (R' : X.NaturalRep x) : X.NaturalRep x :=
  R.restrict _ (R.isOpen_connectedComponentIn_inter R')
    (R.isConnected_connectedComponentIn_inter R') (R.mem_connectedComponentIn_inter R')
    ((connectedComponentIn_subset _ _).trans inter_subset_left)
    (R.mapsTo_Φ_connectedComponentIn R')

/-- **Uniqueness of the natural representation**: restricted to the connected component of `x`
in `U ∩ U'`, two natural representations at `x` agree: same `U`, same `Φ`, same `Γ` there. -/
theorem restrictInter_eq (R' : X.NaturalRep x) :
    (R.restrictInter R').U = (R'.restrictInter R).U ∧
      (∀ g, EqOn ((R.restrictInter R').Φ g) ((R'.restrictInter R).Φ g) (R.restrictInter R').U) ∧
      ∀ g, EqOn ((R.restrictInter R').Γ g) ((R'.restrictInter R).Γ g) (R.restrictInter R').U :=
  ⟨by change connectedComponentIn _ x = connectedComponentIn _ x; rw [inter_comm],
    fun g => R.Φ_eqOn R' g, fun g => R.Γ_eqOn R' g⟩

/-! ### The action `Φ̂` of `G_x` on the morphisms of `U(x)` (pp. 232–233) -/

/-- **`Φ̂(g)`** on `𝐔(x)`: `Φ̂(g)(φ) = Γ(g, t φ) ∘ φ ∘ Γ(g, s φ)⁻¹` (conjugation by `Γ(g, ·)`;
`Φhat_Γ` is the text's definition `Φ̂(g)(φ) = Γ(g h g⁻¹, g ∗ s(φ))` for `φ ∈ 𝐔(h)`). -/
def Φhat (g : X.Isotropy x) (φ : Mor) : Mor :=
  X.comp (X.comp (R.Γ g (X.tgt φ)) φ) (X.inv (R.Γ g (X.src φ)))

/-- **The text's formula**: `Φ̂(g)(Γ(h, y)) = Γ(g h g⁻¹, g ∗ y)` (p. 232). -/
theorem Φhat_Γ (g h : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) :
    R.Φhat g (R.Γ h y) = R.Γ (g * h * g⁻¹) (R.Φ g y) := by
  unfold Φhat
  rw [R.src_Γ h y hy, R.tgt_Γ h y hy, R.Γ_mul g h hy, ← R.Γ_inv g hy,
    ← R.Γ_mul (g * h) g⁻¹ (R.mapsTo_Φ g hy), R.Φ_inv_Φ g hy]

/-- `Φ̂(g)` maps the sheet `𝐔(h)` into `𝐔(g h g⁻¹)`. -/
theorem Φhat_mem_image (g h : X.Isotropy x) {φ : Mor} (hφ : φ ∈ R.Γ h '' R.U) :
    R.Φhat g φ ∈ R.Γ (g * h * g⁻¹) '' R.U := by
  obtain ⟨y, hy, rfl⟩ := hφ
  rw [R.Φhat_Γ g h hy]
  exact R.Γ_mem_image _ (R.mapsTo_Φ g hy)

/-- The sheet index of `Φ̂(g)(φ)` is `g h g⁻¹`, `h` the sheet index of `φ`. -/
theorem index_Φhat (g : X.Isotropy x) {φ : Mor} (hφ : φ ∈ X.morOn R.U) :
    R.index (R.Φhat g φ) = g * R.index φ * g⁻¹ := by
  conv_lhs => rw [← R.Γ_index hφ]
  rw [R.Φhat_Γ g _ hφ.1, R.index_Γ _ (R.mapsTo_Φ g hφ.1)]

/-- `s(Φ̂(g)(φ)) = g ∗ s(φ)`. -/
theorem src_Φhat (g : X.Isotropy x) {φ : Mor} (hφ : φ ∈ X.morOn R.U) :
    X.src (R.Φhat g φ) = R.Φ g (X.src φ) := by
  obtain ⟨h, hh⟩ := R.exists_Γ_eq hφ
  rw [← hh, R.Φhat_Γ g h hφ.1, R.src_Γ _ _ (R.mapsTo_Φ g hφ.1), R.src_Γ h _ hφ.1]

/-- `Φ(g h g⁻¹)(g ∗ y) = g ∗ (h ∗ y)`. -/
theorem Φ_conj (g h : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) :
    R.Φ (g * h * g⁻¹) (R.Φ g y) = R.Φ g (R.Φ h y) := by
  rw [R.Φ_mul _ _ _ (R.mapsTo_Φ g hy), R.Φ_inv_Φ g hy, R.Φ_mul _ _ _ hy]

/-- `t(Φ̂(g)(φ)) = g ∗ t(φ)`. -/
theorem tgt_Φhat (g : X.Isotropy x) {φ : Mor} (hφ : φ ∈ X.morOn R.U) :
    X.tgt (R.Φhat g φ) = R.Φ g (X.tgt φ) := by
  obtain ⟨h, hh⟩ := R.exists_Γ_eq hφ
  rw [← hh, R.Φhat_Γ g h hφ.1, R.tgt_Γ _ _ (R.mapsTo_Φ g hφ.1), R.tgt_Γ h _ hφ.1,
    R.Φ_conj g h hφ.1]

theorem mapsTo_Φhat (g : X.Isotropy x) : MapsTo (R.Φhat g) (X.morOn R.U) (X.morOn R.U) :=
  fun φ hφ => ⟨by rw [R.src_Φhat g hφ]; exact R.mapsTo_Φ g hφ.1,
    by rw [R.tgt_Φhat g hφ]; exact R.mapsTo_Φ g hφ.2⟩

/-- `Φ̂(1) = id` on `𝐔(x)`. -/
theorem Φhat_one {φ : Mor} (hφ : φ ∈ X.morOn R.U) : R.Φhat 1 φ = φ := by
  obtain ⟨h, hh⟩ := R.exists_Γ_eq hφ
  rw [← hh, R.Φhat_Γ 1 h hφ.1, one_mul, inv_one, mul_one, R.Φ_one _ hφ.1]

/-- **`Φ̂` is a homomorphism**: `Φ̂(g g') = Φ̂(g) ∘ Φ̂(g')` on `𝐔(x)` (p. 233). -/
theorem Φhat_mul (g g' : X.Isotropy x) {φ : Mor} (hφ : φ ∈ X.morOn R.U) :
    R.Φhat (g * g') φ = R.Φhat g (R.Φhat g' φ) := by
  obtain ⟨h, hh⟩ := R.exists_Γ_eq hφ
  rw [← hh, R.Φhat_Γ _ h hφ.1, R.Φhat_Γ g' h hφ.1, R.Φhat_Γ g _ (R.mapsTo_Φ g' hφ.1),
    R.Φ_mul _ _ _ hφ.1, mul_inv_rev]
  simp only [mul_assoc]

/-- **`Φ̂(g)` is sc-smooth on `𝐔(x)`**: on each sheet `𝐔(h)` it is `Γ(g h g⁻¹, ·) ∘ Φ(g) ∘ s`. -/
theorem isScSmoothOn_Φhat (g : X.Isotropy x) :
    X.PMor.IsScSmoothOn X.PMor (R.Φhat g) (X.morOn R.U) := by
  refine MPolyfold.IsScSmoothOn.of_locally R.isOpen_morOn fun φ hφ => ?_
  obtain ⟨h, hh⟩ := R.exists_Γ_eq hφ
  have hφh : φ ∈ R.Γ h '' R.U := ⟨X.src φ, hφ.1, hh⟩
  refine ⟨R.Γ h '' R.U, R.isOpen_image_Γ h, hφh, fun ψ hψ => ?_, ?_⟩
  · rw [← R.iUnion_image_Γ]
    exact mem_iUnion.2 ⟨h, hψ⟩
  have hsrc := (R.isScDiffeoOn_src_image h).isScSmoothOn
  refine (MPolyfold.IsScSmoothOn.comp (R.isScSmoothOn_Γ (g * h * g⁻¹))
    (MPolyfold.IsScSmoothOn.comp (R.isScDiffeoOn_Φ g).isScSmoothOn hsrc
      (R.isScDiffeoOn_src_image h).mapsTo) fun ψ hψ => ?_).congr fun ψ hψ => ?_
  · exact R.mapsTo_Φ g ((R.isScDiffeoOn_src_image h).mapsTo hψ)
  · obtain ⟨y, hy, rfl⟩ := hψ
    simp only [Function.comp_apply]
    rw [R.Φhat_Γ g h hy, R.src_Γ h y hy]

/-- **`Φ̂(g)` is an sc-diffeomorphism of `𝐔(x)`**, with inverse `Φ̂(g⁻¹)` (p. 233). -/
theorem isScDiffeoOn_Φhat (g : X.Isotropy x) :
    X.PMor.IsScDiffeoOn X.PMor (R.Φhat g) (R.Φhat g⁻¹) (X.morOn R.U) (X.morOn R.U) where
  isScSmoothOn := R.isScSmoothOn_Φhat g
  isScSmoothOn_inv := R.isScSmoothOn_Φhat g⁻¹
  mapsTo := R.mapsTo_Φhat g
  mapsTo_inv := R.mapsTo_Φhat g⁻¹
  left_inv φ hφ := by rw [← R.Φhat_mul _ _ hφ, inv_mul_cancel, R.Φhat_one hφ]
  right_inv φ hφ := by rw [← R.Φhat_mul _ _ hφ, mul_inv_cancel, R.Φhat_one hφ]

/-- `Φ̂(g)(𝐔(h)) = 𝐔(g h g⁻¹)` (p. 233). -/
theorem image_Φhat (g h : X.Isotropy x) :
    R.Φhat g '' (R.Γ h '' R.U) = R.Γ (g * h * g⁻¹) '' R.U := by
  refine Subset.antisymm (image_subset_iff.2 fun φ hφ => R.Φhat_mem_image g h hφ) fun ψ hψ => ?_
  have hψU : ψ ∈ X.morOn R.U := R.iUnion_image_Γ ▸ mem_iUnion.2 ⟨_, hψ⟩
  refine ⟨R.Φhat g⁻¹ ψ, ?_, ?_⟩
  · have h1 := R.Φhat_mem_image g⁻¹ _ hψ
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at h1
  · rw [← R.Φhat_mul _ _ hψU, mul_inv_cancel, R.Φhat_one hψU]

/-! ### `G_x ⋉ U(x)` as an ep-groupoid (p. 232) -/

/-- The isotropy group is finite (Proposition 7.4; the argument of Lemma 7.1). -/
private theorem finite_isotropy : Finite (X.Isotropy x) := by
  have hfin := MPolyfold.finite_isotropy_of_isLocalScDiffeo X.isLocalScDiffeo_tgt
    (X.exists_isProperMap x)
  have := hfin.to_subtype
  exact Finite.of_injective (fun g : X.Isotropy x =>
    (⟨g.val, g.src_val, g.tgt_val⟩ : {φ | X.src φ = x ∧ X.tgt φ = x}))
    fun g h hgh => GroupoidStr.Isotropy.ext (congrArg Subtype.val hgh)

/-- The discrete topology on `G_x` (the text's "finite group `G`"). -/
scoped instance instTopologicalSpaceIsotropy : TopologicalSpace (X.Isotropy x) := ⊥

scoped instance : DiscreteTopology (X.Isotropy x) := ⟨rfl⟩

scoped instance : Nonempty R.U := ⟨⟨x, R.mem_U⟩⟩

scoped instance : ParacompactSpace R.U := X.PObj.paracompactSpace_subtype R.U

/-- **The M-polyfold `U(x)`**, an open subset of `X` (`MPolyfold.restrictOpen`). -/
def objPolyfold : MPolyfold R.U := X.PObj.restrictOpen R.isOpen_U

scoped instance : ParacompactSpace (X.Isotropy x × R.U) :=
  MPolyfold.paracompactSpace_prod (discretePolyfold (X.Isotropy x)) R.objPolyfold

/-- **The M-polyfold `G_x × U(x)`**: `#G_x` copies of `U(x)` (`Discrete.lean`). -/
def morPolyfold : MPolyfold (X.Isotropy x × R.U) := (discretePolyfold _).prod R.objPolyfold

/-- `y ↦ g ∗ y` is sc-smooth on the M-polyfold `U(x)`. -/
theorem isScSmoothMap_smul (g : X.Isotropy x) :
    R.objPolyfold.IsScSmoothMap R.objPolyfold fun y : R.U => g • y :=
  MPolyfold.IsScSmoothMap.codRestrict_restrictOpen R.isOpen_U
    (MPolyfold.IsScSmoothOn.comp (R.isScDiffeoOn_Φ g).isScSmoothOn
      (isScSmoothMap_restrictOpen_val X.PObj R.isOpen_U) fun y _ => y.2) _

theorem continuous_smul' (g : X.Isotropy x) : Continuous fun y : R.U => g • y :=
  continuousOn_univ.1 (R.isScSmoothMap_smul g).continuousOn

theorem continuous_smul_prod : Continuous fun p : X.Isotropy x × R.U => p.1 • p.2 :=
  continuous_prod_of_discrete_left.2 fun g => R.continuous_smul' g

/-- `(g, y) ↦ (g, g ∗ y)`, a homeomorphism of `G_x × U`. -/
def shearHomeomorph : X.Isotropy x × R.U ≃ₜ X.Isotropy x × R.U where
  toFun p := (p.1, p.1 • p.2)
  invFun p := (p.1, p.1⁻¹ • p.2)
  left_inv p := Prod.ext rfl (inv_smul_smul p.1 p.2)
  right_inv p := Prod.ext rfl (smul_inv_smul p.1 p.2)
  continuous_toFun := continuous_fst.prodMk R.continuous_smul_prod
  continuous_invFun := continuous_fst.prodMk
    (continuous_prod_of_discrete_left.2 fun g => R.continuous_smul' g⁻¹)

/-- `s(g, y) = y` is a local sc-diffeomorphism `G_x × U → U`. -/
theorem translation_isLocalScDiffeo_src :
    R.morPolyfold.IsLocalScDiffeo R.objPolyfold R.translationGroupoid.src := fun p =>
  ⟨{p.1} ×ˢ univ, univ, fun y => (p.1, y), ⟨rfl, mem_univ _⟩, isScDiffeoOn_snd_sheet p.1⟩

/-- `t(g, y) = g ∗ y` is a local sc-diffeomorphism `G_x × U → U`. -/
theorem translation_isLocalScDiffeo_tgt :
    R.morPolyfold.IsLocalScDiffeo R.objPolyfold R.translationGroupoid.tgt := fun p => by
  refine ⟨{p.1} ×ˢ univ, univ, fun z => (p.1, p.1⁻¹ • z), ⟨rfl, mem_univ _⟩, ?_⟩
  exact
    { isScSmoothOn := (MPolyfold.IsScSmoothOn.comp (R.isScSmoothMap_smul p.1)
        ((MPolyfold.isScSmoothMap_snd _ _).mono (isOpen_sheet p.1) (subset_univ _))
        (mapsTo_univ _ _)).congr fun q hq => by
          change p.1 • q.2 = q.1 • q.2
          rw [show q.1 = p.1 from hq.1]
      isScSmoothOn_inv := (isScSmoothMap_sheet p.1).comp (R.isScSmoothMap_smul p.1⁻¹)
      mapsTo := mapsTo_univ _ _
      mapsTo_inv := fun _ _ => ⟨rfl, mem_univ _⟩
      left_inv := fun q hq => Prod.ext (show p.1 = q.1 from (hq.1 : q.1 = p.1).symm) (by
        change p.1⁻¹ • q.1 • q.2 = q.2
        rw [show q.1 = p.1 from hq.1, inv_smul_smul])
      right_inv := fun z _ => smul_inv_smul p.1 z }

/-- Condition (4) for `G_x ⋉ U`, in the sheet form: `ψ ↦ σ(t ψ) ∘ ψ = (k(ψ) h, y)` has a locally
constant first component and the second component `y`. -/
theorem translation_isScSmoothCompSheet :
    IsScSmoothCompSheet R.objPolyfold R.morPolyfold R.translationGroupoid.src
      R.translationGroupoid.tgt R.translationGroupoid.comp := by
  intro σ W V hd
  have hTo : IsOpen ((fun p : X.Isotropy x × R.U => p.1 • p.2) ⁻¹' V) :=
    hd.isScSmoothOn_inv.isOpen.preimage R.continuous_smul_prod
  have h1 : ContinuousOn (fun ψ : X.Isotropy x × R.U => σ (ψ.1 • ψ.2))
      ((fun p : X.Isotropy x × R.U => p.1 • p.2) ⁻¹' V) :=
    hd.isScSmoothOn_inv.continuousOn.comp R.continuous_smul_prod.continuousOn fun _ hψ => hψ
  have h2 : ContinuousOn (fun ψ : X.Isotropy x × R.U => (σ (ψ.1 • ψ.2)).1 * ψ.1)
      ((fun p : X.Isotropy x × R.U => p.1 • p.2) ⁻¹' V) :=
    (continuous_of_discreteTopology (f := fun a : X.Isotropy x × X.Isotropy x => a.1 * a.2)
      ).comp_continuousOn ((continuous_fst.comp_continuousOn h1).prodMk
        continuous_fst.continuousOn)
  exact MPolyfold.IsScSmoothOn.prodMk (isScSmoothOn_discrete_of_continuousOn hTo h2)
    ((MPolyfold.isScSmoothMap_snd _ _).mono hTo (subset_univ _))

/-- `t : s⁻¹(cl V) → U` is proper for every `V`: `t = π₂ ∘ (g, y) ↦ (g, g ∗ y)` with `G_x`
finite. -/
theorem translation_isProperMap (V : Set R.U) :
    IsProperMap ((R.translationGroupoid.src ⁻¹' closure V).domRestrict
      R.translationGroupoid.tgt) := by
  have := finite_isotropy (X := X) (x := x)
  have h : IsProperMap fun p : X.Isotropy x × R.U => p.1 • p.2 :=
    isProperMap_snd_of_compactSpace.comp R.shearHomeomorph.isProperMap
  exact h.restrict (isClosed_closure.preimage continuous_snd)

/-- **`G_x ⋉ U(x)` is an ep-groupoid** (p. 232): objects the M-polyfold `U(x)`, morphisms
`G_x × U(x)`. -/
def translationEpGroupoid : EpGroupoid R.U (X.Isotropy x × R.U) where
  toGroupoidStr := R.translationGroupoid
  PObj := R.objPolyfold
  PMor := R.morPolyfold
  isLocalScDiffeo_src := R.translation_isLocalScDiffeo_src
  isLocalScDiffeo_tgt := R.translation_isLocalScDiffeo_tgt
  isScSmoothMap_unit := isScSmoothMap_sheet 1
  isScSmoothMap_inv := isScSmoothMap_prod_discrete_iff.2 fun g =>
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete g⁻¹) (R.isScSmoothMap_smul g)
  exists_isProperMap _ := ⟨univ, isOpen_univ, mem_univ _, R.translation_isProperMap univ⟩
  isScSmoothComp := (isScSmoothComp_iff_sheet _ _).2 R.translation_isScSmoothCompSheet

/-- **`Γ : G_x ⋉ U(x) → X` is a morphism of `EP`** (Definition 7.7): the functor `functor`,
sc-smooth on objects (the inclusion `U ⊆ X`) and on morphisms (`Γ(g, ·)` on each sheet). -/
def epFunctor : EpFunctor R.translationEpGroupoid X where
  toGroupoidFunctor := R.functor
  isScSmoothMap_obj := isScSmoothMap_restrictOpen_val X.PObj R.isOpen_U
  isScSmoothMap_mor := isScSmoothMap_prod_discrete_iff.2 fun g => by
    have h := MPolyfold.IsScSmoothOn.comp (R.isScSmoothOn_Γ g)
      (isScSmoothMap_restrictOpen_val X.PObj R.isOpen_U) fun y _ => y.2
    exact h

end NaturalRep

end EpGroupoid

end Polyfold
