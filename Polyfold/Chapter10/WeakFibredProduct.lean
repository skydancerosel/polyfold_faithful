import Polyfold.Chapter10.Equivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.2 "The Weak Fibered Product" (pp. 477–483; 2017: pp. 342–347):
**Definition 10.2.1** (2017: Definition 10.3) and the first claim of **Theorem 10.2.2** (2017:
Theorem 10.2), that the weak fibred product is an ep-groupoid, with the parts of the proof that
build its structure.  Numbers and pages are the 2021 text's, the 2017 ones in parentheses.  The
other claims of Theorem 10.2.2 and Remark 10.2.3 are in `WeakFibredProductTheorem.lean`.

# The weak fibred product of sc-smooth functors

## The text, paraphrased

(Definition 10.2.1, p. 477 (2017: Definition 10.3, p. 342)) For sc-smooth functors `F : X → Y`
and `G : Z → Y` of ep-groupoids, the weak fibred product `L = X ×_Y Z` has as objects the
triples `(x, ϕ, z)` with `ϕ : F(x) → G(z)` a morphism of `Y` (`L = X _F×ₛ 𝐘 ₜ×_G Z`) and as
morphisms the triples `(h, ϕ, k) ∈ 𝐗 × 𝐘 × 𝐙` with `s(F(h)) = s(ϕ)` and `s(G(k)) = t(ϕ)`.  The
unit is `(1_x, ϕ, 1_z)`, the inverse `(h⁻¹, G(k) ∘ ϕ ∘ F(h)⁻¹, k⁻¹)`, the source
`(s(h), ϕ, s(k))`, the target `(t(h), G(k) ∘ ϕ ∘ F(h)⁻¹, t(k))` and the product
`(h ∘ h', ϕ', k ∘ k')`.  `L` is a groupoid; by Theorem 2.9 of the text's reference [56] it is an
ep-groupoid when `F` or `G` is an equivalence, and the text gives a modified proof.

(Theorem 10.2.2, first claim, p. 477, and its proof, pp. 478–481) For an equivalence `F` and an
sc-smooth `G`, `L` is in a natural way an ep-groupoid; `L` and `𝐋` carry the structures of
sub-M-polyfolds of `X × 𝐘 × Z` and `𝐗 × 𝐘 × 𝐙`.  *Proof* (text): near `(x, ϕ, z)` take open sets
on which `F`, `s`, `t` are sc-diffeomorphisms and `V ∋ z` with `G(V)` inside the image of `t`;
the map (10.8), `(x', ϕ', z') ↦ ((F|)⁻¹(s((t|)⁻¹(G z'))), (t|)⁻¹(G z'), z')`, is an
sc-retraction onto `L`, and in the induced charts `πZ` is the identity, so `πZ` is a local
sc-diffeomorphism (10.9); the same for `𝐋` and `π_𝐙` (10.10).  The structure maps are sc-smooth
and `s`, `t` are local sc-diffeomorphisms by commutative diagrams with `πZ` and `π_𝐙`
(`t = s ∘ ι`).  Properness: with `U ∋ x`, `V ∋ z` for which `t : s⁻¹(U) → X` and
`t : s⁻¹(V) → Z` are proper and `W = {(x', ϕ', z') | x' ∈ U, z' ∈ V}`, a sequence
`(h_n, ψ_n, k_n)` over `W` with convergent targets has subsequences `h_n → h`, `k_n → k`, and then
`ψ_n → G(k)⁻¹ ∘ ψ' ∘ F(h)`.

## What is formalized (namespace `Polyfold.WeakFibredProduct`)

* Helpers: `MPolyfold.IsLocalScDiffeo.of_comm` (a continuous lift `f` with `p₂ ∘ f = g ∘ p₁` of
  local sc-diffeomorphisms is one), `MPolyfold.isLocalScDiffeo_snd_fibredProduct`,
  `MPolyfold.isLocalScDiffeo_fst_fibredProduct`, `EpGroupoid.isScSmoothOn_comp_of` (`a(p) ∘ b(p)`
  is sc-smooth for sc-smooth composable `a, b`), `EpGroupoid.tendsto_comp`.
* **Definition 10.2.1**: the sets `objRight G = 𝐘 ₜ×_G Z`, `objSet F G`, the type `Obj F G` of
  objects with `Obj.x`, `Obj.φ`, `Obj.z`, `Obj.mk`, `Obj.ext`; `morRight G`, `morSet F G`, `Mor F G`
  with `Mor.h`, `Mor.φ`, `Mor.k`, `Mor.mk`, `Mor.ext`; `conj F G h ϕ k = G(k) ∘ ϕ ∘ F(h)⁻¹` with
  `src_conj`, `tgt_conj`, `conj_comp_mor` (naturality), `conj_recover`, `conj_inv`, `conj_unit`,
  `conj_comp`; the structure maps `src`, `tgt`, `unit`, `inv`, `comp` (`compOf` on composable
  pairs, `comp_eq_compOf`, `src_eq_tgt_iff`), the groupoid laws (`src_comp`, …, `inv_comp`) and
  the groupoid `groupoid F G`.
* Topology, for all `F`, `G`: `continuous_src`, `continuous_tgt`, `continuous_conj`,
  `continuous_obj_of`, `continuous_mor_of`; **properness** `exists_isProperMap`
  (Definition 7.1.3 (3)).
* M-polyfolds: `Admissible F G` (`F` or `G` is a local sc-diffeomorphism on objects); `PA G`,
  `PB G`, `PObj F G h`, `PMor F G h` with `isSubMPolyfold_objSet`, `isSubMPolyfold_morSet`;
  sc-smoothness of the entries (`isScSmoothMap_x`, …, `isScSmoothMap_conj`) and of maps into `L`
  and `𝐋` (`isScSmoothOn_obj_of`, `isScSmoothOn_mor_of`); (10.9), (10.10) as
  `isLocalScDiffeo_z`, `isLocalScDiffeo_k` (for `F` a local sc-diffeomorphism) and
  `isLocalScDiffeo_x`, `isLocalScDiffeo_h` (for `G` one); conditions (1), (2), (4) of Definition
  7.1.3 as `isLocalScDiffeo_src`, `isLocalScDiffeo_tgt`, `isScSmoothMap_unit`,
  `isScSmoothMap_inv`, `isScSmoothComp`.
* **Theorem 10.2.2, first claim**: `epGroupoid F G h : EpGroupoid (Obj F G) (Mor F G)`.

## What the text leaves implicit, and the choices made

* **Triples as iterated fibred products.**  An object is `(x, (ϕ, z))` with `(ϕ, z)` in the
  fibred product `𝐘 ₜ×_G Z ⊆ 𝐘 × Z` and `F(x) = s(ϕ)`; a morphism is `(h, (ϕ, k))` with
  `(ϕ, k) ∈ 𝐘 ₜ×_{G∘s} 𝐙` and `F(s(h)) = s(ϕ)`.  The M-polyfold structures are the iterated
  sub-M-polyfold structures of Part I (Proposition 2.3.19, `MPolyfold.subPolyfold`; Proposition
  2.5.20, `MPolyfold.isSubMPolyfold_fibredProduct`): `𝐘 ₜ×_G Z ⊆ 𝐘 × Z` since `t` is a local
  sc-diffeomorphism, then `L ⊆ X × (𝐘 ₜ×_G Z)` since `F` is one.  We read the text's
  "sub-M-polyfold of `X × 𝐘 × Z`" in this form; the two retractions of Part I's proof of Proposition
  2.5.20 (`fibredSubDataL`) play the role of the text's (10.8), and the comparison with a
  structure induced from the triple product is not needed below.
* **Hypothesis.**  The construction uses about `F` only that it is a local sc-diffeomorphism on
  objects (the text's proof uses nothing else for this part); fullness, faithfulness and
  essential surjectivity enter only in "`πZ` is an equivalence".  `epGroupoid` takes
  `Admissible F G`: `F` *or* `G` a local sc-diffeomorphism.  The second case is the text's "if `G`
  is an equivalence instead" (`isSubMPolyfold_fibredProduct'`, and `πX`, `π_𝐗` in place of `πZ`,
  `π_𝐙`); since the hypothesis is a proposition, both cases give the same ep-groupoid.
* **Sc-smoothness** of `s`, `t`, `u`, `ι`, `m` is proved entrywise (a map into a sub-M-polyfold is
  sc-smooth if it is into the ambient M-polyfold, as in Chapter 7's `SubGroupoid.lean`; the middle
  entry `G(k) ∘ ϕ ∘ F(h)⁻¹` by condition (4) of `Y` in the sheet form); the local
  sc-diffeomorphism property of `s` and `t` follows from the diagrams `πZ ∘ s = s_Z ∘ π_𝐙`,
  `πZ ∘ t = t_Z ∘ π_𝐙` (`IsLocalScDiffeo.of_comm`), so `t = s ∘ ι` is not needed.
* `m` is a total map (as Chapter 7's `GroupoidStr`); off the composable pairs its value is the
  first argument, and condition (4) only concerns `𝐋 ₛ×ₜ 𝐋`.
* **Properness** holds for all `F`, `G`.  The text's "`t : s⁻¹(U) → X` proper" is read with
  `cl U`, as in Definition 7.1.3 (3); `cl W` lies over `cl U` and `cl V`.  The sequential argument
  is `isProperMap_domRestrict_iff_of_isClosed` (all spaces are metrizable); the limit is
  `(h, G(k)⁻¹ ∘ ψ' ∘ F(h), k)`, using `ψ_n = G(k_n)⁻¹ ∘ (G(k_n) ∘ ψ_n ∘ F(h_n)⁻¹) ∘ F(h_n)`
  (`conj_recover`) and the continuity of `m` on composable pairs.
* In Definition 10.2.1 the inverse is printed `ι(h, ψ, k) := (h⁻¹, G(k) ∘ ϕ ∘ F(h)⁻¹, k⁻¹)`; we
  read `ψ` as `ϕ` (possible misprint).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v w

/-! ### Helpers on M-polyfolds and ep-groupoids -/

section Helpers

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {PM : MPolyfold M}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ParacompactSpace N] {PN : MPolyfold N}

/-- A map into a sub-M-polyfold `A ⊆ N` which is sc-smooth into `N` is sc-smooth into `A` (near
`x`, `f = (i⁻¹ ∘ r) ∘ i ∘ f`; a copy of a private lemma of `Chapter7/SubGroupoid.lean`). -/
private theorem isScSmoothOn_subPolyfold_of_val {A : Set N} (hA : PN.IsSubMPolyfold A)
    [ParacompactSpace A] {f : M → A} {U : Set M}
    (hf : PM.IsScSmoothOn PN (fun x => (f x : N)) U) :
    PM.IsScSmoothOn (MPolyfold.subPolyfold hA) f U := by
  refine MPolyfold.IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : N)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (MPolyfold.subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

/-- **A continuous lift of local sc-diffeomorphisms is one**: if `p₂ ∘ f = g ∘ p₁` with `p₁`,
`p₂`, `g` local sc-diffeomorphisms and `f` continuous, then `f` is a local sc-diffeomorphism
(near `x`, `f = (p₂|)⁻¹ ∘ g ∘ p₁`; the commutative diagrams of the proof of Theorem 10.2.2). -/
theorem MPolyfold.IsLocalScDiffeo.of_comm {M₁ M₂ N₁ N₂ : Type*}
    [TopologicalSpace M₁] [T2Space M₁] [ParacompactSpace M₁] [TopologicalSpace M₂] [T2Space M₂]
    [ParacompactSpace M₂] [TopologicalSpace N₁] [T2Space N₁] [ParacompactSpace N₁]
    [TopologicalSpace N₂] [T2Space N₂] [ParacompactSpace N₂] {P₁ : MPolyfold M₁}
    {P₂ : MPolyfold M₂} {Q₁ : MPolyfold N₁} {Q₂ : MPolyfold N₂} {f : M₁ → M₂} {p₁ : M₁ → N₁}
    {p₂ : M₂ → N₂} {g : N₁ → N₂} (hf : Continuous f) (hp₁ : P₁.IsLocalScDiffeo Q₁ p₁)
    (hp₂ : P₂.IsLocalScDiffeo Q₂ p₂) (hg : Q₁.IsLocalScDiffeo Q₂ g)
    (hc : ∀ x, p₂ (f x) = g (p₁ x)) : P₁.IsLocalScDiffeo P₂ f := fun x =>
  MPolyfold.IsLocalScDiffeoAt.of_comp_left (hp₂.at (f x)) hf
    (((hg.comp hp₁).at x).congr (Eventually.of_forall fun y => (hc y).symm))

end Helpers

section FibredHelpers

variable {X : Type u} {Y : Type v} {Z : Type w} [TopologicalSpace X] [T2Space X]
  [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] [TopologicalSpace Z]
  [T2Space Z] [ParacompactSpace Z] {P : MPolyfold X} {Q : MPolyfold Y} {S : MPolyfold Z}
  [ParacompactSpace (X × Y)] {f : X → Z} {g : Y → Z}
  [ParacompactSpace (MPolyfold.fibredProduct f g)]
  (hA : (P.prod Q).IsSubMPolyfold (MPolyfold.fibredProduct f g))

/-- For a local sc-diffeomorphism `f`, the projection `X ₓ×_g Y → Y` is a local
sc-diffeomorphism (the proof of Proposition 2.5.20; preprint 2.46). -/
theorem MPolyfold.isLocalScDiffeo_snd_fibredProduct (hf : P.IsLocalScDiffeo S f)
    (hg : Q.IsScSmoothMap S g) :
    (MPolyfold.subPolyfold hA).IsLocalScDiffeo Q fun a : MPolyfold.fibredProduct f g => a.1.2 :=
  fun a => by
    obtain ⟨U, V, h, hx, hd⟩ := hf a.1.1
    refine ⟨_, _, _, ?_, MPolyfold.isScDiffeoOn_snd_fibredProduct hA hd hg a⟩
    refine ⟨hx, ?_⟩
    change g a.1.2 ∈ V
    rw [← show f a.1.1 = g a.1.2 from a.2]
    exact hd.mapsTo hx

/-- For a local sc-diffeomorphism `g`, the projection `X ₓ×_g Y → X` is a local
sc-diffeomorphism. -/
theorem MPolyfold.isLocalScDiffeo_fst_fibredProduct (hf : P.IsScSmoothMap S f)
    (hg : Q.IsLocalScDiffeo S g) :
    (MPolyfold.subPolyfold hA).IsLocalScDiffeo P fun a : MPolyfold.fibredProduct f g => a.1.1 :=
  fun a => by
    obtain ⟨U, V, k, hy, hd⟩ := hg a.1.2
    refine ⟨_, _, _, ?_, MPolyfold.isScDiffeoOn_fst_fibredProduct hA hd hf a⟩
    refine ⟨?_, hy⟩
    change f a.1.1 ∈ V
    rw [show f a.1.1 = g a.1.2 from a.2]
    exact hd.mapsTo hy

end FibredHelpers

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  {M : Type*} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {PM : MPolyfold M}

/-- **Composites of sc-smooth families are sc-smooth**: for sc-smooth `a, b : M → 𝐗` with
`s(a(p)) = t(b(p))`, the map `p ↦ a(p) ∘ b(p)` is sc-smooth (condition (4) of Definition 7.1.3 in
the sheet form, as `EpNatTrans.isScSmoothMap_comp_app`). -/
theorem isScSmoothOn_comp_of {a b : M → Mor} {U : Set M} (ha : PM.IsScSmoothOn X.PMor a U)
    (hb : PM.IsScSmoothOn X.PMor b U) (hab : ∀ p ∈ U, X.src (a p) = X.tgt (b p)) :
    PM.IsScSmoothOn X.PMor (fun p => X.comp (a p) (b p)) U := by
  refine MPolyfold.IsScSmoothOn.of_locally ha.isOpen fun p₀ hp₀ => ?_
  obtain ⟨W, V, σ, hW, hd⟩ := X.isLocalScDiffeo_src (a p₀)
  have hU' : IsOpen (U ∩ a ⁻¹' W) :=
    ha.continuousOn.isOpen_inter_preimage ha.isOpen hd.isOpen_source
  have hmaps : MapsTo b (U ∩ a ⁻¹' W) (X.tgt ⁻¹' V) := fun p hp => by
    change X.tgt (b p) ∈ V
    rw [← hab p hp.1]
    exact hd.mapsTo hp.2
  refine ⟨U ∩ a ⁻¹' W, hU', ⟨hp₀, hW⟩, inter_subset_left, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (X.isScSmoothCompSheet σ W V hd)
    (hb.mono hU' inter_subset_left) hmaps).congr fun p hp => ?_
  simp only [Function.comp_apply]
  rw [← hab p hp.1, hd.left_inv _ hp.2]

/-- **Composition is continuous along filters**: if `a → a₀`, `b → b₀` with `s(a) = t(b)` and
`s(a₀) = t(b₀)`, then `a ∘ b → a₀ ∘ b₀`. -/
theorem tendsto_comp {α : Type*} {l : Filter α} {a b : α → Mor} {a₀ b₀ : Mor}
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀)) (hab : ∀ n, X.src (a n) = X.tgt (b n))
    (h₀ : X.src a₀ = X.tgt b₀) :
    Tendsto (fun n => X.comp (a n) (b n)) l (𝓝 (X.comp a₀ b₀)) := by
  have h : Tendsto (fun n => (⟨(a n, b n), hab n⟩ : MPolyfold.fibredProduct X.src X.tgt)) l
      (𝓝 ⟨(a₀, b₀), h₀⟩) := tendsto_subtype_rng.2 (ha.prodMk_nhds hb)
  exact ((X.continuous_comp_fibredProduct.tendsto _).comp h)

end EpGroupoid

/-! ### The weak fibred product: objects and morphisms -/

section WFP

variable {ObjX MorX : Type u} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type v} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjZ MorZ : Type w} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY} {Z : EpGroupoid ObjZ MorZ}
  (F : EpFunctor X Y) (G : EpFunctor Z Y)

namespace WeakFibredProduct

/-- The pairs `(ϕ, z) ∈ 𝐘 × Z` with `t(ϕ) = G(z)`: the fibred product `𝐘 ₜ×_G Z`. -/
abbrev objRight : Set (MorY × ObjZ) := MPolyfold.fibredProduct Y.tgt G.obj

/-- The object set `L = X _F×ₛ 𝐘 ₜ×_G Z` of Definition 10.2.1: pairs `(x, (ϕ, z))` with
`(ϕ, z) ∈ 𝐘 ₜ×_G Z` and `F(x) = s(ϕ)`. -/
abbrev objSet : Set (ObjX × objRight G) := MPolyfold.fibredProduct F.obj fun a => Y.src a.1.1

/-- The objects `(x, ϕ, z)` of the weak fibred product, `ϕ : F(x) → G(z)`. -/
abbrev Obj := ↥(objSet F G)

/-- The pairs `(ϕ, k) ∈ 𝐘 × 𝐙` with `t(ϕ) = G(s(k))`. -/
abbrev morRight : Set (MorY × MorZ) := MPolyfold.fibredProduct Y.tgt fun k => G.obj (Z.src k)

/-- The morphism set `𝐋 = 𝐗 _{s∘F}×ₛ 𝐘 ₜ×_{s∘G} 𝐙` of Definition 10.2.1. -/
abbrev morSet : Set (MorX × morRight G) :=
  MPolyfold.fibredProduct (fun h => F.obj (X.src h)) fun b => Y.src b.1.1

/-- The morphisms `(h, ϕ, k)` of the weak fibred product, `ϕ : F(s(h)) → G(s(k))`. -/
abbrev Mor := ↥(morSet F G)

variable {F G}

namespace Obj

/-- The entry `x` of `(x, ϕ, z)`. -/
def x (p : Obj F G) : ObjX := p.1.1

/-- The entry `ϕ` of `(x, ϕ, z)`. -/
def φ (p : Obj F G) : MorY := p.1.2.1.1

/-- The entry `z` of `(x, ϕ, z)`. -/
def z (p : Obj F G) : ObjZ := p.1.2.1.2

theorem src_φ (p : Obj F G) : Y.src p.φ = F.obj p.x := p.2.symm

theorem tgt_φ (p : Obj F G) : Y.tgt p.φ = G.obj p.z := p.1.2.2

variable (F G) in
/-- The object `(x, ϕ, z)`. -/
def mk (x : ObjX) (φ : MorY) (z : ObjZ) (h₁ : Y.src φ = F.obj x) (h₂ : Y.tgt φ = G.obj z) :
    Obj F G :=
  ⟨(x, ⟨(φ, z), h₂⟩), h₁.symm⟩

@[simp] theorem mk_x (x : ObjX) (φ : MorY) (z : ObjZ) (h₁ h₂) :
    (mk F G x φ z h₁ h₂).x = x := rfl

@[simp] theorem mk_φ (x : ObjX) (φ : MorY) (z : ObjZ) (h₁ h₂) :
    (mk F G x φ z h₁ h₂).φ = φ := rfl

@[simp] theorem mk_z (x : ObjX) (φ : MorY) (z : ObjZ) (h₁ h₂) :
    (mk F G x φ z h₁ h₂).z = z := rfl

@[ext]
theorem ext {p q : Obj F G} (hx : p.x = q.x) (hφ : p.φ = q.φ) (hz : p.z = q.z) : p = q :=
  Subtype.ext (Prod.ext hx (Subtype.ext (Prod.ext hφ hz)))

end Obj

namespace Mor

/-- The entry `h` of `(h, ϕ, k)`. -/
def h (m : Mor F G) : MorX := m.1.1

/-- The entry `ϕ` of `(h, ϕ, k)`. -/
def φ (m : Mor F G) : MorY := m.1.2.1.1

/-- The entry `k` of `(h, ϕ, k)`. -/
def k (m : Mor F G) : MorZ := m.1.2.1.2

theorem src_φ (m : Mor F G) : Y.src m.φ = F.obj (X.src m.h) := m.2.symm

theorem tgt_φ (m : Mor F G) : Y.tgt m.φ = G.obj (Z.src m.k) := m.1.2.2

variable (F G) in
/-- The morphism `(h, ϕ, k)`. -/
def mk (h : MorX) (φ : MorY) (k : MorZ) (h₁ : Y.src φ = F.obj (X.src h))
    (h₂ : Y.tgt φ = G.obj (Z.src k)) : Mor F G :=
  ⟨(h, ⟨(φ, k), h₂⟩), h₁.symm⟩

@[simp] theorem mk_h (h : MorX) (φ : MorY) (k : MorZ) (h₁ h₂) :
    (mk F G h φ k h₁ h₂).h = h := rfl

@[simp] theorem mk_φ (h : MorX) (φ : MorY) (k : MorZ) (h₁ h₂) :
    (mk F G h φ k h₁ h₂).φ = φ := rfl

@[simp] theorem mk_k (h : MorX) (φ : MorY) (k : MorZ) (h₁ h₂) :
    (mk F G h φ k h₁ h₂).k = k := rfl

@[ext]
theorem ext {m m' : Mor F G} (hh : m.h = m'.h) (hφ : m.φ = m'.φ) (hk : m.k = m'.k) : m = m' :=
  Subtype.ext (Prod.ext hh (Subtype.ext (Prod.ext hφ hk)))

end Mor

/-! ### The groupoid algebra in `Y` -/

variable (F G) in
/-- `G(k) ∘ ϕ ∘ F(h)⁻¹`, the middle entry of `t(h, ϕ, k)` and of `ι(h, ϕ, k)`. -/
def conj (h : MorX) (φ : MorY) (k : MorZ) : MorY :=
  Y.comp (Y.comp (G.mor k) φ) (Y.inv (F.mor h))

section Algebra

variable {h : MorX} {φ : MorY} {k : MorZ}

private theorem conj_aux₁ (h₂ : Y.tgt φ = G.obj (Z.src k)) : Y.src (G.mor k) = Y.tgt φ := by
  rw [G.src_mor, h₂]

private theorem conj_aux₂ (h₁ : Y.src φ = F.obj (X.src h)) (h₂ : Y.tgt φ = G.obj (Z.src k)) :
    Y.src (Y.comp (G.mor k) φ) = Y.tgt (Y.inv (F.mor h)) := by
  rw [Y.src_comp _ _ (conj_aux₁ h₂), Y.tgt_inv, F.src_mor, h₁]

theorem src_conj (h₁ : Y.src φ = F.obj (X.src h)) (h₂ : Y.tgt φ = G.obj (Z.src k)) :
    Y.src (conj F G h φ k) = F.obj (X.tgt h) := by
  rw [conj, Y.src_comp _ _ (conj_aux₂ h₁ h₂), Y.src_inv, F.tgt_mor]

theorem tgt_conj (h₁ : Y.src φ = F.obj (X.src h)) (h₂ : Y.tgt φ = G.obj (Z.src k)) :
    Y.tgt (conj F G h φ k) = G.obj (Z.tgt k) := by
  rw [conj, Y.tgt_comp _ _ (conj_aux₂ h₁ h₂), Y.tgt_comp _ _ (conj_aux₁ h₂), G.tgt_mor]

/-- **Naturality**: `(G(k) ∘ ϕ ∘ F(h)⁻¹) ∘ F(h) = G(k) ∘ ϕ`. -/
theorem conj_comp_mor (h₁ : Y.src φ = F.obj (X.src h)) (h₂ : Y.tgt φ = G.obj (Z.src k)) :
    Y.comp (conj F G h φ k) (F.mor h) = Y.comp (G.mor k) φ := by
  rw [conj, Y.comp_assoc _ _ _ (conj_aux₂ h₁ h₂) (Y.src_inv _), Y.inv_comp,
    GroupoidStr.comp_unit_of_eq (G := Y.toGroupoidStr)
      (by rw [Y.src_comp _ _ (conj_aux₁ h₂), h₁, F.src_mor])]

/-- `ϕ = G(k)⁻¹ ∘ (G(k) ∘ ϕ ∘ F(h)⁻¹) ∘ F(h)`. -/
theorem conj_recover (h₁ : Y.src φ = F.obj (X.src h)) (h₂ : Y.tgt φ = G.obj (Z.src k)) :
    Y.comp (Y.comp (Y.inv (G.mor k)) (conj F G h φ k)) (F.mor h) = φ := by
  have e₁ := conj_aux₁ h₂
  have e₃ : Y.src (Y.inv (G.mor k)) = Y.tgt (conj F G h φ k) := by
    rw [Y.src_inv, conj, Y.tgt_comp _ _ (conj_aux₂ h₁ h₂), Y.tgt_comp _ _ e₁]
  have e₄ : Y.src (conj F G h φ k) = Y.tgt (F.mor h) := by
    rw [src_conj h₁ h₂, F.tgt_mor]
  rw [Y.comp_assoc _ _ _ e₃ e₄, conj_comp_mor h₁ h₂, GroupoidStr.inv_comp_cancel_left e₁]

/-- `ι` is involutive on the middle entry: `G(k⁻¹) ∘ (G(k) ∘ ϕ ∘ F(h)⁻¹) ∘ F(h⁻¹)⁻¹ = ϕ`. -/
theorem conj_inv (h₁ : Y.src φ = F.obj (X.src h)) (h₂ : Y.tgt φ = G.obj (Z.src k)) :
    conj F G (X.inv h) (conj F G h φ k) (Z.inv k) = φ := by
  change Y.comp (Y.comp (G.mor (Z.inv k)) (conj F G h φ k)) (Y.inv (F.mor (X.inv h))) = φ
  rw [F.mor_inv, G.mor_inv, GroupoidStr.inv_inv]
  exact conj_recover h₁ h₂

/-- `G(1_z) ∘ ϕ ∘ F(1_x)⁻¹ = ϕ`. -/
theorem conj_unit {x : ObjX} {z : ObjZ} (h₁ : Y.src φ = F.obj x) (h₂ : Y.tgt φ = G.obj z) :
    conj F G (X.unit x) φ (Z.unit z) = φ := by
  rw [conj, F.mor_unit, G.mor_unit, GroupoidStr.inv_unit, GroupoidStr.unit_comp_of_eq h₂,
    GroupoidStr.comp_unit_of_eq h₁]

end Algebra

/-- `t(h, ϕ, k)` after `t(h', ϕ', k')`: `G(k ∘ k') ∘ ϕ' ∘ F(h ∘ h')⁻¹ =
G(k) ∘ (G(k') ∘ ϕ' ∘ F(h')⁻¹) ∘ F(h)⁻¹`. -/
theorem conj_comp {h h' : MorX} {φ' : MorY} {k k' : MorZ} (hh : X.src h = X.tgt h')
    (hk : Z.src k = Z.tgt k') (h₁ : Y.src φ' = F.obj (X.src h'))
    (h₂ : Y.tgt φ' = G.obj (Z.src k')) :
    conj F G (X.comp h h') φ' (Z.comp k k') = conj F G h (conj F G h' φ' k') k := by
  -- the right side has the form `(Gk ∘ ψ) ∘ F(h)⁻¹`; we compare after composing with `F(h ∘ h')`
  set ψ := conj F G h' φ' k' with hψ
  have hψs : Y.src ψ = F.obj (X.tgt h') := src_conj h₁ h₂
  have hψt : Y.tgt ψ = G.obj (Z.tgt k') := tgt_conj h₁ h₂
  have h₁' : Y.src ψ = F.obj (X.src h) := by rw [hψs, hh]
  have h₂' : Y.tgt ψ = G.obj (Z.src k) := by rw [hψt, hk]
  have h₁'' : Y.src φ' = F.obj (X.src (X.comp h h')) := by rw [X.src_comp _ _ hh, h₁]
  have h₂'' : Y.tgt φ' = G.obj (Z.src (Z.comp k k')) := by rw [Z.src_comp _ _ hk, h₂]
  refine GroupoidStr.comp_right_cancel (G := Y.toGroupoidStr) (φ := F.mor (X.comp h h'))
    ?_ ?_ ?_
  · rw [src_conj h₁'' h₂'', F.tgt_mor]
  · rw [src_conj h₁' h₂', F.tgt_mor, X.tgt_comp _ _ hh]
  · have eF : F.mor (X.comp h h') = Y.comp (F.mor h) (F.mor h') :=
      F.mor_comp _ _ hh
    have eG : G.mor (Z.comp k k') = Y.comp (G.mor k) (G.mor k') := G.mor_comp _ _ hk
    have a₁ : Y.src (G.mor k) = Y.tgt (G.mor k') := by rw [G.src_mor, G.tgt_mor, hk]
    have a₂ : Y.src (G.mor k') = Y.tgt φ' := by rw [G.src_mor, h₂]
    have a₃ : Y.src (G.mor k) = Y.tgt ψ := by rw [G.src_mor, h₂']
    have a₄ : Y.src (F.mor h) = Y.tgt (F.mor h') := by rw [F.src_mor, F.tgt_mor, hh]
    have a₅ : Y.src (conj F G h ψ k) = Y.tgt (F.mor h) := by
      rw [src_conj h₁' h₂', F.tgt_mor]
    have a₆ : Y.src (Y.comp (conj F G h ψ k) (F.mor h)) = Y.tgt (F.mor h') := by
      rw [Y.src_comp _ _ a₅, F.src_mor, F.tgt_mor, hh]
    have a₇ : Y.src ψ = Y.tgt (F.mor h') := by rw [hψs, F.tgt_mor]
    rw [conj_comp_mor h₁'' h₂'', eF, eG, ← Y.comp_assoc _ _ _ a₅ a₄, conj_comp_mor h₁' h₂',
      Y.comp_assoc _ _ _ a₃ a₇, hψ, conj_comp_mor h₁ h₂, Y.comp_assoc _ _ _ a₁ a₂]

/-! ### Definition 10.2.1: the structure maps -/

/-- `s(h, ϕ, k) = (s(h), ϕ, s(k))`. -/
def src (m : Mor F G) : Obj F G := Obj.mk F G (X.src m.h) m.φ (Z.src m.k) m.src_φ m.tgt_φ

/-- `t(h, ϕ, k) = (t(h), G(k) ∘ ϕ ∘ F(h)⁻¹, t(k))`. -/
def tgt (m : Mor F G) : Obj F G :=
  Obj.mk F G (X.tgt m.h) (conj F G m.h m.φ m.k) (Z.tgt m.k) (src_conj m.src_φ m.tgt_φ)
    (tgt_conj m.src_φ m.tgt_φ)

/-- `1_{(x, ϕ, z)} = (1_x, ϕ, 1_z)`. -/
def unit (p : Obj F G) : Mor F G :=
  Mor.mk F G (X.unit p.x) p.φ (Z.unit p.z) (by rw [X.src_unit]; exact p.src_φ)
    (by rw [Z.src_unit]; exact p.tgt_φ)

/-- `ι(h, ϕ, k) = (h⁻¹, G(k) ∘ ϕ ∘ F(h)⁻¹, k⁻¹)`. -/
def inv (m : Mor F G) : Mor F G :=
  Mor.mk F G (X.inv m.h) (conj F G m.h m.φ m.k) (Z.inv m.k)
    (by rw [X.src_inv]; exact src_conj m.src_φ m.tgt_φ)
    (by rw [Z.src_inv]; exact tgt_conj m.src_φ m.tgt_φ)

@[simp] theorem x_src (m : Mor F G) : (src m).x = X.src m.h := rfl
@[simp] theorem φ_src (m : Mor F G) : (src m).φ = m.φ := rfl
@[simp] theorem z_src (m : Mor F G) : (src m).z = Z.src m.k := rfl
@[simp] theorem x_tgt (m : Mor F G) : (tgt m).x = X.tgt m.h := rfl
@[simp] theorem φ_tgt (m : Mor F G) : (tgt m).φ = conj F G m.h m.φ m.k := rfl
@[simp] theorem z_tgt (m : Mor F G) : (tgt m).z = Z.tgt m.k := rfl
@[simp] theorem h_unit (p : Obj F G) : (unit p).h = X.unit p.x := rfl
@[simp] theorem φ_unit (p : Obj F G) : (unit p).φ = p.φ := rfl
@[simp] theorem k_unit (p : Obj F G) : (unit p).k = Z.unit p.z := rfl
@[simp] theorem h_inv (m : Mor F G) : (inv m).h = X.inv m.h := rfl
@[simp] theorem φ_inv (m : Mor F G) : (inv m).φ = conj F G m.h m.φ m.k := rfl
@[simp] theorem k_inv (m : Mor F G) : (inv m).k = Z.inv m.k := rfl

/-- Composable pairs: `s(h, ϕ, k) = t(h', ϕ', k')` means `s(h) = t(h')`,
`ϕ = G(k') ∘ ϕ' ∘ F(h')⁻¹` and `s(k) = t(k')`. -/
theorem src_eq_tgt_iff {m m' : Mor F G} : src m = tgt m' ↔
    X.src m.h = X.tgt m'.h ∧ m.φ = conj F G m'.h m'.φ m'.k ∧ Z.src m.k = Z.tgt m'.k :=
  ⟨fun hc => ⟨congrArg Obj.x hc, congrArg Obj.φ hc, congrArg Obj.z hc⟩,
    fun ⟨hx, hφ, hz⟩ => Obj.ext hx hφ hz⟩

/-- The product `(h ∘ h', ϕ', k ∘ k')` of a composable pair. -/
def compOf (m m' : Mor F G) (hc : src m = tgt m') : Mor F G :=
  Mor.mk F G (X.comp m.h m'.h) m'.φ (Z.comp m.k m'.k)
    (by rw [X.src_comp _ _ (src_eq_tgt_iff.1 hc).1]; exact m'.src_φ)
    (by rw [Z.src_comp _ _ (src_eq_tgt_iff.1 hc).2.2]; exact m'.tgt_φ)

open scoped Classical in
/-- `m((h, ϕ, k), (h', ϕ', k')) = (h ∘ h', ϕ', k ∘ k')`, a total map whose value off the
composable pairs (the first argument) is not used. -/
def comp (m m' : Mor F G) : Mor F G := if hc : src m = tgt m' then compOf m m' hc else m

theorem comp_eq_compOf {m m' : Mor F G} (hc : src m = tgt m') : comp m m' = compOf m m' hc :=
  dif_pos hc

theorem h_comp {m m' : Mor F G} (hc : src m = tgt m') : (comp m m').h = X.comp m.h m'.h := by
  rw [comp_eq_compOf hc]; rfl

theorem φ_comp {m m' : Mor F G} (hc : src m = tgt m') : (comp m m').φ = m'.φ := by
  rw [comp_eq_compOf hc]; rfl

theorem k_comp {m m' : Mor F G} (hc : src m = tgt m') : (comp m m').k = Z.comp m.k m'.k := by
  rw [comp_eq_compOf hc]; rfl

/-! ### Definition 10.2.1: the groupoid laws -/

theorem src_comp {m m' : Mor F G} (hc : src m = tgt m') : src (comp m m') = src m' := by
  obtain ⟨hx, -, hz⟩ := src_eq_tgt_iff.1 hc
  refine Obj.ext ?_ ?_ ?_
  · rw [x_src, h_comp hc, X.src_comp _ _ hx]; rfl
  · rw [φ_src, φ_comp hc]; rfl
  · rw [z_src, k_comp hc, Z.src_comp _ _ hz]; rfl

theorem tgt_comp {m m' : Mor F G} (hc : src m = tgt m') : tgt (comp m m') = tgt m := by
  obtain ⟨hx, hφ, hz⟩ := src_eq_tgt_iff.1 hc
  refine Obj.ext ?_ ?_ ?_
  · rw [x_tgt, h_comp hc, X.tgt_comp _ _ hx]; rfl
  · rw [φ_tgt, φ_tgt, h_comp hc, φ_comp hc, k_comp hc, conj_comp hx hz m'.src_φ m'.tgt_φ, hφ]
  · rw [z_tgt, k_comp hc, Z.tgt_comp _ _ hz]; rfl

theorem comp_assoc {m m' m'' : Mor F G} (h₁ : src m = tgt m') (h₂ : src m' = tgt m'') :
    comp (comp m m') m'' = comp m (comp m' m'') := by
  have h₃ : src (comp m m') = tgt m'' := (src_comp h₁).trans h₂
  have h₄ : src m = tgt (comp m' m'') := h₁.trans (tgt_comp h₂).symm
  obtain ⟨hx₁, -, hz₁⟩ := src_eq_tgt_iff.1 h₁
  obtain ⟨hx₂, -, hz₂⟩ := src_eq_tgt_iff.1 h₂
  refine Mor.ext ?_ ?_ ?_
  · rw [h_comp h₃, h_comp h₁, h_comp h₄, h_comp h₂, X.comp_assoc _ _ _ hx₁ hx₂]
  · rw [φ_comp h₃, φ_comp h₄, φ_comp h₂]
  · rw [k_comp h₃, k_comp h₁, k_comp h₄, k_comp h₂, Z.comp_assoc _ _ _ hz₁ hz₂]

theorem src_unit (p : Obj F G) : src (unit p) = p := Obj.ext (X.src_unit _) rfl (Z.src_unit _)

theorem tgt_unit (p : Obj F G) : tgt (unit p) = p :=
  Obj.ext (X.tgt_unit _) (conj_unit p.src_φ p.tgt_φ) (Z.tgt_unit _)

theorem comp_unit (m : Mor F G) : comp m (unit (src m)) = m := by
  have hc : src m = tgt (unit (src m)) := (tgt_unit _).symm
  refine Mor.ext ?_ ?_ ?_
  · rw [h_comp hc]; exact X.comp_unit _
  · rw [φ_comp hc]; rfl
  · rw [k_comp hc]; exact Z.comp_unit _

theorem unit_comp (m : Mor F G) : comp (unit (tgt m)) m = m := by
  have hc : src (unit (tgt m)) = tgt m := src_unit _
  refine Mor.ext ?_ ?_ ?_
  · rw [h_comp hc]; exact X.unit_comp _
  · rw [φ_comp hc]
  · rw [k_comp hc]; exact Z.unit_comp _

theorem src_inv (m : Mor F G) : src (inv m) = tgt m := Obj.ext (X.src_inv _) rfl (Z.src_inv _)

theorem tgt_inv (m : Mor F G) : tgt (inv m) = src m :=
  Obj.ext (X.tgt_inv _) (conj_inv m.src_φ m.tgt_φ) (Z.tgt_inv _)

theorem comp_inv (m : Mor F G) : comp m (inv m) = unit (tgt m) := by
  have hc : src m = tgt (inv m) := (tgt_inv m).symm
  refine Mor.ext ?_ ?_ ?_
  · rw [h_comp hc]; exact X.comp_inv _
  · rw [φ_comp hc]; rfl
  · rw [k_comp hc]; exact Z.comp_inv _

theorem inv_comp (m : Mor F G) : comp (inv m) m = unit (src m) := by
  have hc : src (inv m) = tgt m := src_inv m
  refine Mor.ext ?_ ?_ ?_
  · rw [h_comp hc]; exact X.inv_comp _
  · rw [φ_comp hc]; rfl
  · rw [k_comp hc]; exact Z.inv_comp _

variable (F G) in
/-- **2021 Definition 10.2.1, p. 477 (2017: Definition 10.3, p. 342)**: the **weak fibred
product** `L = X ×_Y Z` of sc-smooth functors `F : X → Y`, `G : Z → Y`, as a groupoid: objects
`(x, ϕ, z)` with `ϕ : F(x) → G(z)`, morphisms `(h, ϕ, k)` with `ϕ : F(s(h)) → G(s(k))`,
`1 = (1_x, ϕ, 1_z)`, `ι(h, ϕ, k) = (h⁻¹, G(k) ∘ ϕ ∘ F(h)⁻¹, k⁻¹)`,
`s(h, ϕ, k) = (s(h), ϕ, s(k))`, `t(h, ϕ, k) = (t(h), G(k) ∘ ϕ ∘ F(h)⁻¹, t(k))`,
`m((h, ϕ, k), (h', ϕ', k')) = (h ∘ h', ϕ', k ∘ k')`. -/
def groupoid : GroupoidStr (Obj F G) (Mor F G) where
  src := src
  tgt := tgt
  comp := comp
  unit := unit
  inv := inv
  src_comp _ _ h := src_comp h
  tgt_comp _ _ h := tgt_comp h
  comp_assoc _ _ _ h₁ h₂ := comp_assoc h₁ h₂
  src_unit := src_unit
  tgt_unit := tgt_unit
  comp_unit := comp_unit
  unit_comp := unit_comp
  src_inv := src_inv
  tgt_inv := tgt_inv
  comp_inv := comp_inv
  inv_comp := inv_comp

/-! ### The topology: continuity of the structure maps -/

theorem continuous_x : Continuous (Obj.x : Obj F G → ObjX) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_toRight : Continuous fun p : Obj F G => (p.1.2 : MorY × ObjZ) :=
  continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)

theorem continuous_φ : Continuous (Obj.φ : Obj F G → MorY) := continuous_fst.comp continuous_toRight

theorem continuous_z : Continuous (Obj.z : Obj F G → ObjZ) := continuous_snd.comp continuous_toRight

theorem continuous_h : Continuous (Mor.h : Mor F G → MorX) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_morToRight : Continuous fun m : Mor F G => (m.1.2 : MorY × MorZ) :=
  continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)

theorem continuous_mφ : Continuous (Mor.φ : Mor F G → MorY) :=
  continuous_fst.comp continuous_morToRight

theorem continuous_k : Continuous (Mor.k : Mor F G → MorZ) :=
  continuous_snd.comp continuous_morToRight

/-- A map into the objects is continuous if its three entries are. -/
theorem continuous_obj_of {α : Type*} [TopologicalSpace α] {f : α → Obj F G}
    (hx : Continuous fun a => (f a).x) (hφ : Continuous fun a => (f a).φ)
    (hz : Continuous fun a => (f a).z) : Continuous f :=
  (hx.prodMk ((hφ.prodMk hz).subtype_mk fun a => (f a).1.2.2)).subtype_mk fun a => (f a).2

/-- A map into the morphisms is continuous if its three entries are. -/
theorem continuous_mor_of {α : Type*} [TopologicalSpace α] {f : α → Mor F G}
    (hh : Continuous fun a => (f a).h) (hφ : Continuous fun a => (f a).φ)
    (hk : Continuous fun a => (f a).k) : Continuous f :=
  (hh.prodMk ((hφ.prodMk hk).subtype_mk fun a => (f a).1.2.2)).subtype_mk fun a => (f a).2

/-- `(h, ϕ, k) ↦ G(k) ∘ ϕ ∘ F(h)⁻¹` is continuous. -/
theorem continuous_conj : Continuous fun m : Mor F G => conj F G m.h m.φ m.k := by
  refine Y.continuous_comp_fibredProduct.comp
    (((Y.continuous_comp_fibredProduct.comp
      (((G.continuous_mor.comp continuous_k).prodMk continuous_mφ).subtype_mk fun m => ?_)).prodMk
      (Y.continuous_inv.comp (F.continuous_mor.comp continuous_h))).subtype_mk fun m => ?_)
  · exact (G.src_mor _).trans m.tgt_φ.symm
  · change Y.src (Y.comp (G.mor m.k) m.φ) = Y.tgt (Y.inv (F.mor m.h))
    rw [Y.src_comp _ _ ((G.src_mor _).trans m.tgt_φ.symm), Y.tgt_inv, F.src_mor, m.src_φ]

theorem continuous_src : Continuous (src : Mor F G → Obj F G) :=
  continuous_obj_of (X.continuous_src.comp continuous_h) continuous_mφ
    (Z.continuous_src.comp continuous_k)

theorem continuous_tgt : Continuous (tgt : Mor F G → Obj F G) :=
  continuous_obj_of (X.continuous_tgt.comp continuous_h) continuous_conj
    (Z.continuous_tgt.comp continuous_k)

/-! ### Condition (3) of Definition 7.1.3: properness -/

/-- **Properness** (the proof of Theorem 10.2.2, "Next we will show that `L` is proper"): for
`(x, ϕ, z)` and open `U ∋ x`, `V ∋ z` with the properness property in `X` and `Z`, the open
`W = {(x', ϕ', z') | x' ∈ U, z' ∈ V}` has `t : s⁻¹(cl W) → L` proper.  Sequentially: a subsequence
of `h_n` converges (properness of `U`), then one of `k_n` (properness of `V`), and
`ϕ_n = G(k_n)⁻¹ ∘ (G(k_n) ∘ ϕ_n ∘ F(h_n)⁻¹) ∘ F(h_n)` converges by continuity of `m`. -/
theorem exists_isProperMap (p₀ : Obj F G) : ∃ W : Set (Obj F G), IsOpen W ∧ p₀ ∈ W ∧
    IsProperMap ((src ⁻¹' closure W).domRestrict (tgt : Mor F G → Obj F G)) := by
  obtain ⟨U, hUo, hxU, hU⟩ := X.exists_isProperMap p₀.x
  obtain ⟨V, hVo, hzV, hV⟩ := Z.exists_isProperMap p₀.z
  refine ⟨Obj.x ⁻¹' U ∩ Obj.z ⁻¹' V, (hUo.preimage continuous_x).inter
    (hVo.preimage continuous_z), ⟨hxU, hzV⟩, ?_⟩
  have := X.PMor.metrizableSpace
  have := Y.PMor.metrizableSpace
  have := Z.PMor.metrizableSpace
  have := X.PObj.metrizableSpace
  have := Z.PObj.metrizableSpace
  rw [Polyfold.isProperMap_domRestrict_iff_of_isClosed continuous_src continuous_tgt
    isClosed_closure]
  intro φ y hφ hy
  have hcl : ∀ n, X.src (φ n).h ∈ closure U ∧ Z.src (φ n).k ∈ closure V := fun n => by
    have h1 := closure_inter_subset_inter_closure _ _ (hφ n)
    exact ⟨continuous_x.closure_preimage_subset U h1.1,
      continuous_z.closure_preimage_subset V h1.2⟩
  have hyx : Tendsto (X.tgt ∘ fun n => (φ n).h) atTop (𝓝 y.x) :=
    (continuous_x.tendsto y).comp hy
  have hyz : Tendsto (Z.tgt ∘ fun n => (φ n).k) atTop (𝓝 y.z) :=
    (continuous_z.tendsto y).comp hy
  have hyφ : Tendsto (fun n => conj F G (φ n).h (φ n).φ (φ n).k) atTop (𝓝 y.φ) :=
    (continuous_φ.tendsto y).comp hy
  obtain ⟨h₀, -, hh₀, ψ₁, hψ₁, hlim₁⟩ :=
    MPolyfold.exists_tendsto_subseq_of_isProperMap_domRestrict X.PMor hU
      (fun n => (hcl n).1) hyx
  obtain ⟨k₀, -, hk₀, ψ₂, hψ₂, hlimk⟩ :=
    MPolyfold.exists_tendsto_subseq_of_isProperMap_domRestrict Z.PMor hV
      (φ := fun n => (φ (ψ₁ n)).k) (fun n => (hcl (ψ₁ n)).2) (hyz.comp hψ₁.tendsto_atTop)
  have hlimh : Tendsto (fun n => (φ (ψ₁ (ψ₂ n))).h) atTop (𝓝 h₀) :=
    hlim₁.comp hψ₂.tendsto_atTop
  have hlimc : Tendsto (fun n => conj F G (φ (ψ₁ (ψ₂ n))).h (φ (ψ₁ (ψ₂ n))).φ
      (φ (ψ₁ (ψ₂ n))).k) atTop (𝓝 y.φ) := hyφ.comp (hψ₁.comp hψ₂).tendsto_atTop
  set m : ℕ → Mor F G := fun n => φ (ψ₁ (ψ₂ n)) with hm
  -- the limit of the middle entries
  have c₁ : ∀ n, Y.src (Y.inv (G.mor (m n).k)) = Y.tgt (conj F G (m n).h (m n).φ (m n).k) :=
    fun n => by rw [Y.src_inv, G.tgt_mor, tgt_conj (m n).src_φ (m n).tgt_φ]
  have c₀ : Y.src (Y.inv (G.mor k₀)) = Y.tgt y.φ := by
    rw [Y.src_inv, G.tgt_mor, hk₀, y.tgt_φ]
  have c₁' : ∀ n, Y.src (Y.comp (Y.inv (G.mor (m n).k)) (conj F G (m n).h (m n).φ (m n).k)) =
      Y.tgt (F.mor (m n).h) := fun n => by
    rw [Y.src_comp _ _ (c₁ n), src_conj (m n).src_φ (m n).tgt_φ, F.tgt_mor]
  have c₀' : Y.src (Y.comp (Y.inv (G.mor k₀)) y.φ) = Y.tgt (F.mor h₀) := by
    rw [Y.src_comp _ _ c₀, y.src_φ, F.tgt_mor, hh₀]
  have hlimφ : Tendsto (fun n => (m n).φ) atTop
      (𝓝 (Y.comp (Y.comp (Y.inv (G.mor k₀)) y.φ) (F.mor h₀))) := by
    have hinv : Tendsto (fun n => Y.inv (G.mor (m n).k)) atTop (𝓝 (Y.inv (G.mor k₀))) :=
      ((Y.continuous_inv.comp G.continuous_mor).tendsto k₀).comp hlimk
    have hF : Tendsto (fun n => F.mor (m n).h) atTop (𝓝 (F.mor h₀)) :=
      (F.continuous_mor.tendsto h₀).comp hlimh
    refine ((Y.tendsto_comp (Y.tendsto_comp hinv hlimc c₁ c₀) hF c₁' c₀').congr fun n => ?_)
    exact conj_recover (m n).src_φ (m n).tgt_φ
  refine ⟨Mor.mk F G h₀ (Y.comp (Y.comp (Y.inv (G.mor k₀)) y.φ) (F.mor h₀)) k₀ ?_ ?_,
    ψ₁ ∘ ψ₂, hψ₁.comp hψ₂, ?_⟩
  · rw [Y.src_comp _ _ c₀', F.src_mor]
  · rw [Y.tgt_comp _ _ c₀', Y.tgt_comp _ _ c₀, Y.tgt_inv, G.src_mor]
  · exact tendsto_subtype_rng.2 (hlimh.prodMk_nhds (tendsto_subtype_rng.2
      (hlimφ.prodMk_nhds hlimk)))

/-! ### The M-polyfold structures -/

instance instParacompactSpaceObjRight : ParacompactSpace (objRight G) := by
  have := Y.PMor.metrizableSpace
  have := Z.PObj.metrizableSpace
  exact paracompactSpace_of_metrizableSpace _

instance instParacompactSpaceObj : ParacompactSpace (Obj F G) := by
  have := X.PObj.metrizableSpace
  have := Y.PMor.metrizableSpace
  have := Z.PObj.metrizableSpace
  exact paracompactSpace_of_metrizableSpace _

instance instParacompactSpaceMorRight : ParacompactSpace (morRight G) := by
  have := Y.PMor.metrizableSpace
  have := Z.PMor.metrizableSpace
  exact paracompactSpace_of_metrizableSpace _

instance instParacompactSpaceMor : ParacompactSpace (Mor F G) := by
  have := X.PMor.metrizableSpace
  have := Y.PMor.metrizableSpace
  have := Z.PMor.metrizableSpace
  exact paracompactSpace_of_metrizableSpace _

variable (F G)

/-- The hypothesis under which the weak fibred product is given an ep-groupoid structure here:
`F` or `G` is a local sc-diffeomorphism on objects (Theorem 10.2.2 assumes that `F`, or `G`, is
an equivalence). -/
def Admissible : Prop :=
  X.PObj.IsLocalScDiffeo Y.PObj F.obj ∨ Z.PObj.IsLocalScDiffeo Y.PObj G.obj

theorem isSubMPolyfold_objRight :
    letI := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
    (Y.PMor.prod Z.PObj).IsSubMPolyfold (objRight G) := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
  exact MPolyfold.isSubMPolyfold_fibredProduct Y.isLocalScDiffeo_tgt G.isScSmoothMap_obj

/-- The M-polyfold `𝐘 ₜ×_G Z`, a sub-M-polyfold of `𝐘 × Z` (2021 Proposition 2.5.20,
`MPolyfold.isSubMPolyfold_fibredProduct`: `t` is a local sc-diffeomorphism). -/
def PA : MPolyfold (objRight G) :=
  letI := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
  MPolyfold.subPolyfold (isSubMPolyfold_objRight G)

theorem isSubMPolyfold_morRight :
    letI := MPolyfold.paracompactSpace_prod Y.PMor Z.PMor
    (Y.PMor.prod Z.PMor).IsSubMPolyfold (morRight G) := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PMor
  exact MPolyfold.isSubMPolyfold_fibredProduct Y.isLocalScDiffeo_tgt
    (G.isScSmoothMap_obj.comp Z.isScSmoothMap_src)

/-- The M-polyfold `𝐘 ₜ×_{G∘s} 𝐙`, a sub-M-polyfold of `𝐘 × 𝐙`. -/
def PB : MPolyfold (morRight G) :=
  letI := MPolyfold.paracompactSpace_prod Y.PMor Z.PMor
  MPolyfold.subPolyfold (isSubMPolyfold_morRight G)

variable {F G}

section Right

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {PM : MPolyfold M}
  {U : Set M}

theorem isScSmoothMap_PA_fst : (PA G).IsScSmoothMap Y.PMor fun a : objRight G => a.1.1 := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
  exact (MPolyfold.isScSmoothMap_fst Y.PMor Z.PObj).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth _)

theorem isScSmoothMap_PA_snd : (PA G).IsScSmoothMap Z.PObj fun a : objRight G => a.1.2 := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
  exact (MPolyfold.isScSmoothMap_snd Y.PMor Z.PObj).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth _)

theorem isScSmoothMap_PB_fst : (PB G).IsScSmoothMap Y.PMor fun b : morRight G => b.1.1 := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PMor
  exact (MPolyfold.isScSmoothMap_fst Y.PMor Z.PMor).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth _)

theorem isScSmoothMap_PB_snd : (PB G).IsScSmoothMap Z.PMor fun b : morRight G => b.1.2 := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PMor
  exact (MPolyfold.isScSmoothMap_snd Y.PMor Z.PMor).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth _)

theorem isScSmoothOn_PA_of {f : M → objRight G} (h₁ : PM.IsScSmoothOn Y.PMor (fun p => (f p).1.1) U)
    (h₂ : PM.IsScSmoothOn Z.PObj (fun p => (f p).1.2) U) : PM.IsScSmoothOn (PA G) f U := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
  exact isScSmoothOn_subPolyfold_of_val _ (MPolyfold.IsScSmoothOn.prodMk h₁ h₂)

theorem isScSmoothOn_PB_of {f : M → morRight G} (h₁ : PM.IsScSmoothOn Y.PMor (fun p => (f p).1.1) U)
    (h₂ : PM.IsScSmoothOn Z.PMor (fun p => (f p).1.2) U) : PM.IsScSmoothOn (PB G) f U := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PMor
  exact isScSmoothOn_subPolyfold_of_val _ (MPolyfold.IsScSmoothOn.prodMk h₁ h₂)

/-- `(ϕ, z) ↦ z` is a local sc-diffeomorphism `𝐘 ₜ×_G Z → Z` (`t` is one). -/
theorem isLocalScDiffeo_PA_snd : (PA G).IsLocalScDiffeo Z.PObj fun a : objRight G => a.1.2 := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
  exact MPolyfold.isLocalScDiffeo_snd_fibredProduct (isSubMPolyfold_objRight G)
    Y.isLocalScDiffeo_tgt G.isScSmoothMap_obj

/-- `(ϕ, k) ↦ k` is a local sc-diffeomorphism `𝐘 ₜ×_{G∘s} 𝐙 → 𝐙`. -/
theorem isLocalScDiffeo_PB_snd : (PB G).IsLocalScDiffeo Z.PMor fun b : morRight G => b.1.2 := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PMor
  exact MPolyfold.isLocalScDiffeo_snd_fibredProduct (isSubMPolyfold_morRight G)
    Y.isLocalScDiffeo_tgt (G.isScSmoothMap_obj.comp Z.isScSmoothMap_src)

/-- If `G` is a local sc-diffeomorphism, `(ϕ, z) ↦ ϕ` is one. -/
theorem isLocalScDiffeo_PA_fst (hG : Z.PObj.IsLocalScDiffeo Y.PObj G.obj) :
    (PA G).IsLocalScDiffeo Y.PMor fun a : objRight G => a.1.1 := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
  exact MPolyfold.isLocalScDiffeo_fst_fibredProduct (isSubMPolyfold_objRight G)
    Y.isScSmoothMap_tgt hG

/-- If `G` is a local sc-diffeomorphism, `(ϕ, k) ↦ ϕ` is one. -/
theorem isLocalScDiffeo_PB_fst (hG : Z.PObj.IsLocalScDiffeo Y.PObj G.obj) :
    (PB G).IsLocalScDiffeo Y.PMor fun b : morRight G => b.1.1 := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PMor
  exact MPolyfold.isLocalScDiffeo_fst_fibredProduct (isSubMPolyfold_morRight G)
    Y.isScSmoothMap_tgt (hG.comp Z.isLocalScDiffeo_src)

end Right

variable (F G) in
theorem isSubMPolyfold_objSet (h : Admissible F G) :
    letI := MPolyfold.paracompactSpace_prod X.PObj (PA G)
    (X.PObj.prod (PA G)).IsSubMPolyfold (objSet F G) := by
  let _ := MPolyfold.paracompactSpace_prod X.PObj (PA G)
  rcases h with hF | hG
  · exact MPolyfold.isSubMPolyfold_fibredProduct hF (Y.isScSmoothMap_src.comp isScSmoothMap_PA_fst)
  · exact MPolyfold.isSubMPolyfold_fibredProduct' F.isScSmoothMap_obj
      (Y.isLocalScDiffeo_src.comp (isLocalScDiffeo_PA_fst hG))

variable (F G) in
theorem isSubMPolyfold_morSet (h : Admissible F G) :
    letI := MPolyfold.paracompactSpace_prod X.PMor (PB G)
    (X.PMor.prod (PB G)).IsSubMPolyfold (morSet F G) := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor (PB G)
  rcases h with hF | hG
  · exact MPolyfold.isSubMPolyfold_fibredProduct (hF.comp X.isLocalScDiffeo_src)
      (Y.isScSmoothMap_src.comp isScSmoothMap_PB_fst)
  · exact MPolyfold.isSubMPolyfold_fibredProduct' (F.isScSmoothMap_obj.comp X.isScSmoothMap_src)
      (Y.isLocalScDiffeo_src.comp (isLocalScDiffeo_PB_fst hG))

variable (F G) in
/-- **The M-polyfold of objects** `L = X _F×ₛ (𝐘 ₜ×_G Z)`, a sub-M-polyfold of `X × (𝐘 ₜ×_G Z)`
(the natural structure of Theorem 10.2.2, as an iterated fibred product). -/
def PObj (h : Admissible F G) : MPolyfold (Obj F G) :=
  letI := MPolyfold.paracompactSpace_prod X.PObj (PA G)
  MPolyfold.subPolyfold (isSubMPolyfold_objSet F G h)

variable (F G) in
/-- **The M-polyfold of morphisms** `𝐋 = 𝐗 _{F∘s}×ₛ (𝐘 ₜ×_{G∘s} 𝐙)`, a sub-M-polyfold of
`𝐗 × (𝐘 ₜ×_{G∘s} 𝐙)`. -/
def PMor (h : Admissible F G) : MPolyfold (Mor F G) :=
  letI := MPolyfold.paracompactSpace_prod X.PMor (PB G)
  MPolyfold.subPolyfold (isSubMPolyfold_morSet F G h)

section Smooth

variable (h : Admissible F G)
  {M : Type*} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {PM : MPolyfold M}
  {U : Set M}

include h in
theorem isScSmoothMap_x : (PObj F G h).IsScSmoothMap X.PObj Obj.x := by
  let _ := MPolyfold.paracompactSpace_prod X.PObj (PA G)
  exact (MPolyfold.isScSmoothMap_fst X.PObj (PA G)).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth _)

include h in
theorem isScSmoothMap_toRight :
    (PObj F G h).IsScSmoothMap (PA G) fun p : Obj F G => p.1.2 := by
  let _ := MPolyfold.paracompactSpace_prod X.PObj (PA G)
  exact (MPolyfold.isScSmoothMap_snd X.PObj (PA G)).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth _)

theorem isScSmoothMap_φ : (PObj F G h).IsScSmoothMap Y.PMor Obj.φ :=
  isScSmoothMap_PA_fst.comp (isScSmoothMap_toRight h)

theorem isScSmoothMap_z : (PObj F G h).IsScSmoothMap Z.PObj Obj.z :=
  isScSmoothMap_PA_snd.comp (isScSmoothMap_toRight h)

theorem isScSmoothMap_h : (PMor F G h).IsScSmoothMap X.PMor Mor.h := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor (PB G)
  exact (MPolyfold.isScSmoothMap_fst X.PMor (PB G)).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth _)

theorem isScSmoothMap_morToRight :
    (PMor F G h).IsScSmoothMap (PB G) fun m : Mor F G => m.1.2 := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor (PB G)
  exact (MPolyfold.isScSmoothMap_snd X.PMor (PB G)).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth _)

theorem isScSmoothMap_mφ : (PMor F G h).IsScSmoothMap Y.PMor Mor.φ :=
  isScSmoothMap_PB_fst.comp (isScSmoothMap_morToRight h)

theorem isScSmoothMap_k : (PMor F G h).IsScSmoothMap Z.PMor Mor.k :=
  isScSmoothMap_PB_snd.comp (isScSmoothMap_morToRight h)

/-- A map into the objects is sc-smooth if its three entries are. -/
theorem isScSmoothOn_obj_of {f : M → Obj F G} (hx : PM.IsScSmoothOn X.PObj (fun p => (f p).x) U)
    (hφ : PM.IsScSmoothOn Y.PMor (fun p => (f p).φ) U)
    (hz : PM.IsScSmoothOn Z.PObj (fun p => (f p).z) U) : PM.IsScSmoothOn (PObj F G h) f U := by
  let _ := MPolyfold.paracompactSpace_prod X.PObj (PA G)
  exact isScSmoothOn_subPolyfold_of_val _ (MPolyfold.IsScSmoothOn.prodMk hx
    (isScSmoothOn_PA_of (f := fun p => (f p).1.2) hφ hz))

/-- A map into the morphisms is sc-smooth if its three entries are. -/
theorem isScSmoothOn_mor_of {f : M → Mor F G} (hh : PM.IsScSmoothOn X.PMor (fun p => (f p).h) U)
    (hφ : PM.IsScSmoothOn Y.PMor (fun p => (f p).φ) U)
    (hk : PM.IsScSmoothOn Z.PMor (fun p => (f p).k) U) : PM.IsScSmoothOn (PMor F G h) f U := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor (PB G)
  exact isScSmoothOn_subPolyfold_of_val _ (MPolyfold.IsScSmoothOn.prodMk hh
    (isScSmoothOn_PB_of (f := fun p => (f p).1.2) hφ hk))

/-- `(h, ϕ, k) ↦ G(k) ∘ ϕ ∘ F(h)⁻¹` is sc-smooth. -/
theorem isScSmoothMap_conj :
    (PMor F G h).IsScSmoothMap Y.PMor fun m : Mor F G => conj F G m.h m.φ m.k :=
  Y.isScSmoothOn_comp_of
    (Y.isScSmoothOn_comp_of (G.isScSmoothMap_mor.comp (isScSmoothMap_k h)) (isScSmoothMap_mφ h)
      fun m _ => (G.src_mor _).trans m.tgt_φ.symm)
    (Y.isScSmoothMap_inv.comp (F.isScSmoothMap_mor.comp (isScSmoothMap_h h))) fun m _ => by
      rw [Y.src_comp _ _ ((G.src_mor _).trans m.tgt_φ.symm), Y.tgt_inv, F.src_mor, m.src_φ]

/-! #### Conditions (1), (2), (4) of Definition 7.1.3 -/

theorem isScSmoothMap_src : (PMor F G h).IsScSmoothMap (PObj F G h) src :=
  isScSmoothOn_obj_of h (X.isScSmoothMap_src.comp (isScSmoothMap_h h)) (isScSmoothMap_mφ h)
    (Z.isScSmoothMap_src.comp (isScSmoothMap_k h))

theorem isScSmoothMap_tgt : (PMor F G h).IsScSmoothMap (PObj F G h) tgt :=
  isScSmoothOn_obj_of h (X.isScSmoothMap_tgt.comp (isScSmoothMap_h h)) (isScSmoothMap_conj h)
    (Z.isScSmoothMap_tgt.comp (isScSmoothMap_k h))

theorem isScSmoothMap_unit : (PObj F G h).IsScSmoothMap (PMor F G h) unit :=
  isScSmoothOn_mor_of h (X.isScSmoothMap_unit.comp (isScSmoothMap_x h)) (isScSmoothMap_φ h)
    (Z.isScSmoothMap_unit.comp (isScSmoothMap_z h))

theorem isScSmoothMap_inv : (PMor F G h).IsScSmoothMap (PMor F G h) inv :=
  isScSmoothOn_mor_of h (X.isScSmoothMap_inv.comp (isScSmoothMap_h h)) (isScSmoothMap_conj h)
    (Z.isScSmoothMap_inv.comp (isScSmoothMap_k h))

/-- If `F` is a local sc-diffeomorphism, `πZ : (x, ϕ, z) ↦ z` is one (the proof of Theorem
10.2.2: "`πZ` is in our charts the identity map"). -/
theorem isLocalScDiffeo_z (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) :
    (PObj F G h).IsLocalScDiffeo Z.PObj Obj.z := by
  let _ := MPolyfold.paracompactSpace_prod X.PObj (PA G)
  exact isLocalScDiffeo_PA_snd.comp (MPolyfold.isLocalScDiffeo_snd_fibredProduct
    (isSubMPolyfold_objSet F G h) hF (Y.isScSmoothMap_src.comp isScSmoothMap_PA_fst))

/-- If `F` is a local sc-diffeomorphism, `(h, ϕ, k) ↦ k` is one ((10.10) of the text). -/
theorem isLocalScDiffeo_k (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) :
    (PMor F G h).IsLocalScDiffeo Z.PMor Mor.k := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor (PB G)
  exact isLocalScDiffeo_PB_snd.comp (MPolyfold.isLocalScDiffeo_snd_fibredProduct
    (isSubMPolyfold_morSet F G h) (hF.comp X.isLocalScDiffeo_src)
    (Y.isScSmoothMap_src.comp isScSmoothMap_PB_fst))

/-- If `G` is a local sc-diffeomorphism, `πX : (x, ϕ, z) ↦ x` is one. -/
theorem isLocalScDiffeo_x (hG : Z.PObj.IsLocalScDiffeo Y.PObj G.obj) :
    (PObj F G h).IsLocalScDiffeo X.PObj Obj.x := by
  let _ := MPolyfold.paracompactSpace_prod X.PObj (PA G)
  exact MPolyfold.isLocalScDiffeo_fst_fibredProduct (isSubMPolyfold_objSet F G h)
    F.isScSmoothMap_obj (Y.isLocalScDiffeo_src.comp (isLocalScDiffeo_PA_fst hG))

/-- If `G` is a local sc-diffeomorphism, `(h, ϕ, k) ↦ h` is one. -/
theorem isLocalScDiffeo_h (hG : Z.PObj.IsLocalScDiffeo Y.PObj G.obj) :
    (PMor F G h).IsLocalScDiffeo X.PMor Mor.h := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor (PB G)
  exact MPolyfold.isLocalScDiffeo_fst_fibredProduct (isSubMPolyfold_morSet F G h)
    (F.isScSmoothMap_obj.comp X.isScSmoothMap_src)
    (Y.isLocalScDiffeo_src.comp (isLocalScDiffeo_PB_fst hG))

/-- **(1)**: `s` is a local sc-diffeomorphism (the diagram `πZ ∘ s = s_Z ∘ π_𝐙`, or
`πX ∘ s = s_X ∘ π_𝐗`). -/
theorem isLocalScDiffeo_src : (PMor F G h).IsLocalScDiffeo (PObj F G h) src := by
  rcases id h with hF | hG
  · exact MPolyfold.IsLocalScDiffeo.of_comm continuous_src (isLocalScDiffeo_k h hF)
      (isLocalScDiffeo_z h hF) Z.isLocalScDiffeo_src fun _ => rfl
  · exact MPolyfold.IsLocalScDiffeo.of_comm continuous_src (isLocalScDiffeo_h h hG)
      (isLocalScDiffeo_x h hG) X.isLocalScDiffeo_src fun _ => rfl

/-- **(1)**: `t` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_tgt : (PMor F G h).IsLocalScDiffeo (PObj F G h) tgt := by
  rcases id h with hF | hG
  · exact MPolyfold.IsLocalScDiffeo.of_comm continuous_tgt (isLocalScDiffeo_k h hF)
      (isLocalScDiffeo_z h hF) Z.isLocalScDiffeo_tgt fun _ => rfl
  · exact MPolyfold.IsLocalScDiffeo.of_comm continuous_tgt (isLocalScDiffeo_h h hG)
      (isLocalScDiffeo_x h hG) X.isLocalScDiffeo_tgt fun _ => rfl

/-- **(4)**: the multiplication is sc-smooth on `𝐋 ₛ×ₜ 𝐋` (its entries are the multiplications
of `X` and `Z` and a projection). -/
theorem isScSmoothComp : IsScSmoothComp (PObj F G h) (PMor F G h) src tgt comp
    (isLocalScDiffeo_src h) (isLocalScDiffeo_tgt h).isScSmoothMap := by
  let PL := PMor F G h
  let _ := MPolyfold.paracompactSpace_prod PL PL
  let _ := (PL.prod PL).paracompactSpace_subtype
    (MPolyfold.fibredProduct (src : Mor F G → Obj F G) tgt)
  have hFP := MPolyfold.isSubMPolyfold_fibredProduct (isLocalScDiffeo_src h)
    (isLocalScDiffeo_tgt h).isScSmoothMap
  change (MPolyfold.subPolyfold hFP).IsScSmoothMap PL _
  have hi := MPolyfold.subPolyfold_inclusion_isScSmooth hFP
  have h1 : (MPolyfold.subPolyfold hFP).IsScSmoothMap PL fun p => p.1.1 :=
    (MPolyfold.isScSmoothMap_fst PL PL).comp hi
  have h2 : (MPolyfold.subPolyfold hFP).IsScSmoothMap PL fun p => p.1.2 :=
    (MPolyfold.isScSmoothMap_snd PL PL).comp hi
  refine (isScSmoothOn_mor_of h
    (f := fun p : MPolyfold.fibredProduct (src : Mor F G → Obj F G) tgt => compOf p.1.1 p.1.2 p.2)
    (X.isScSmoothOn_comp_of ((isScSmoothMap_h h).comp h1) ((isScSmoothMap_h h).comp h2)
      fun p _ => (src_eq_tgt_iff.1 p.2).1)
    (by have h3 := (isScSmoothMap_mφ h).comp h2; exact h3)
    (Z.isScSmoothOn_comp_of ((isScSmoothMap_k h).comp h1) ((isScSmoothMap_k h).comp h2)
      fun p _ => (src_eq_tgt_iff.1 p.2).2.2)).congr fun p _ => ?_
  exact (comp_eq_compOf p.2).symm

end Smooth

variable (F G) in
/-- **The weak fibred product as an ep-groupoid** (2021 Theorem 10.2.2, p. 477 (2017: Theorem
10.2, p. 343), first claim): when `F` or `G` is a local sc-diffeomorphism on objects (in
particular when one of them is an equivalence), the groupoid of Definition 10.2.1 with the
sub-M-polyfold structures `PObj`, `PMor` is an ep-groupoid. -/
def epGroupoid (h : Admissible F G) : EpGroupoid (Obj F G) (Mor F G) where
  toGroupoidStr := groupoid F G
  PObj := PObj F G h
  PMor := PMor F G h
  isLocalScDiffeo_src := isLocalScDiffeo_src h
  isLocalScDiffeo_tgt := isLocalScDiffeo_tgt h
  isScSmoothMap_unit := isScSmoothMap_unit h
  isScSmoothMap_inv := isScSmoothMap_inv h
  exists_isProperMap := exists_isProperMap
  isScSmoothComp := isScSmoothComp h

end WeakFibredProduct

end WFP

end Polyfold
