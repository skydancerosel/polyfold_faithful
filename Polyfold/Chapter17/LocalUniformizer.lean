import Polyfold.Chapter17.TransitionSet

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 745–749): **Definition 17.1.3** (local uniformizer, footprint, tame), **Remark 17.1.4**,
the transition sets `M(Ψ, Ψ')` of uniformizers (Definition 17.1.5), the bijection
`Ψ̂ : G × O → M(Ψ, Ψ)` of Lemma 17.1.9 (its set-theoretic part), and the bound on p. 749.
Numbers and pages are the 2021 text's.

# Local uniformizers

## The text, paraphrased

(Definition 17.1.3, p. 745) A local uniformizer for the GCT `C` at the object `α` is a functor
`Ψ : G ⋉ O → C` with (1) `G ⋉ O` the translation groupoid of an M-polyfold `O` with an sc-smooth
action of a finite group `G`; (2) `Ψ` injective on objects, `Ψ(q₀) = α` for some `q₀`, and `Ψ`
fully faithful; (3) `|Ψ| : G\O → |C|` a homeomorphism onto an open neighbourhood `U` of `|α|`.
The footprint is `|Ψ(O)|`, open in `|C|`; `Ψ` is tame if `O` is tame.
(Remark 17.1.4, p. 745) The full subcategory on `Ψ(O)` is in bijective functorial correspondence
with `G ⋉ O`, an ep-groupoid; so `Ψ` equips a small full subcategory with an ep-groupoid
structure.  (Lemma 17.1.9, first step of the proof, p. 748) `(g, p) ↦ (p, Ψ(g, p), g ∗ p)` is a
bijection `G × O → M(Ψ, Ψ)`.  (p. 749) For fixed `q ∈ O` there are at most `♯G'` elements
`(q, φ, p) ∈ M(Ψ, Ψ')`: all of them are `(q, Ψ'(g', q'₀) ∘ φ₀, g' ∗ q'₀)` for one of them
`(q, φ₀, q'₀)`.

## What is formalized

* `GroupoidalCategory.Uniformizer C` (**Definition 17.1.3 (1), (2)** without the base point and
  without topology on `C`; the uniformizer of Definition 19.1.2 is this with `IsCentredAt`): the
  M-polyfold `O`, the finite group `G` acting by sc-smooth maps (`smooth_smul`), the functor
  `functor : G ⋉ O → C`, `injective_obj`, `full`, `faithful`.  Accessors `obj`, `mor`, the
  translation ep-groupoid `ep` (Definition 17.1.2), `IsAt α` (`Ψ(q₀) = α` for some `q₀`),
  `FixesPoint`, `IsCentredAt α` (`Ψ(q₀) = α` with `q₀` fixed by `G`).
* Consequences of full faithfulness: `exists_smul_eq_mor`, `mor_injective`, `isotropyEquiv`
  (for `q₀` fixed by `G`, `G ≅ Aut(Ψ(q₀))`), and **Remark 17.1.4** (`remark_17_1_4`: a
  functor `G ⋉ O → C|_{Ψ(O)}` to the full subcategory, bijective on objects and morphisms).
* `Uniformizer.Trans Ψ Ψ'` (**Definition 17.1.5** for uniformizers, `M(Ψ, Ψ')`); `Uniformizer.hat`
  (`Ψ̂`, (17.1)), `hat_bijective`, `hatEquiv`, `src_hat`, `tgt_hat`; `fiberEquiv` (the elements over
  a fixed `q` are a `G'`-torsor), `finite_fiber`, **the bound on p. 749** `ncard_fiber_le`
  (`= ♯G'` when non-empty: `ncard_fiber_eq`), `src_mem_range_iff`.
* `GCT.LocalUniformizer C` (**Definition 17.1.3**): a uniformizer with
  `isOpenEmbedding_orbitMap : IsOpenEmbedding |Ψ|` ((3)); `footprint`, `isOpen_footprint`,
  `mem_footprint_of_isAt`, `continuous_π_obj`, `IsTame`.
* Witnesses: `GCT.LocalUniformizer.tautological` (the identity of a translation GCT `G ⋉ O`) and
  `GCT.LocalUniformizer.reflection` (`ℤ/2 ⋉ ℝ`), centred at `0` with `G = ℤ/2 = Aut(0)`
  (`reflection_isCentredAt`).

## Readings

* A uniformizer is not tied to the object `α`: "at `α`" is the predicate `IsAt α`, and the
  uniformizer construction (Definition 17.1.6) asks it for the members of `F(α)`.
  Definition 17.1.3 (3) asks `|Ψ|` to be a homeomorphism onto an open set containing `|α|`; with
  `IsAt α` this is `IsOpenEmbedding |Ψ|`.
* Definition 17.1.3 does not ask `G` to fix `q₀`, nor `G = G_α`.  Lemma 17.1.9 writes `G = G_α`,
  and Definition 19.1.2 speaks of "the isotropy group".  We formalize Definition 17.1.3 as printed
  and give the predicate `IsCentredAt α`; under it `G ≅ Aut(α)` (`isotropyEquiv`).
* "Full and faithful" are Mathlib's `Functor.Full`, `Functor.Faithful` of
  `GroupoidFunctor.toFunctor`; `exists_smul_eq_mor` and `mor_injective` are the forms used in
  proofs.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-- The quotient map `O → G\O = |G ⋉ O|` of a group acting by homeomorphisms is open:
`π⁻¹(π(W)) = ⋃_g g⁻¹ W`. -/
theorem GroupoidStr.isOpenMap_π_translation {G O : Type u} [Group G] [TopologicalSpace O]
    [MulAction G O] (hc : ∀ g : G, Continuous fun y : O => g • y) :
    IsOpenMap (GroupoidStr.translation G O).π := by
  intro W hW
  refine isOpen_coinduced.2 ?_
  change IsOpen ((GroupoidStr.translation G O).π ⁻¹' _)
  have : (GroupoidStr.translation G O).π ⁻¹' ((GroupoidStr.translation G O).π '' W) =
      ⋃ g : G, (fun y => g • y) ⁻¹' W := by
    ext y
    simp only [mem_preimage, mem_image, mem_iUnion]
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨φ, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 hxy
      refine ⟨φ.1⁻¹, ?_⟩
      change φ.2 = x at h1
      change φ.1 • φ.2 = y at h2
      rw [← h2, inv_smul_smul, h1]
      exact hx
    · rintro ⟨g, hg⟩
      exact ⟨g • y, hg, (GroupoidStr.π_eq_π_iff _).2 ⟨(g⁻¹, g • y), rfl, inv_smul_smul g y⟩⟩
  rw [this]
  exact isOpen_iUnion fun g => hW.preimage (hc g)

namespace GroupoidalCategory

/-- **2021 Definition 17.1.3 (1), (2), p. 745** (without the base point; also Definition 19.1.2,
p. 864, without `Ψ(ō) = α`): a **uniformizer** for the groupoidal category `C`: a fully faithful
functor `Ψ : G ⋉ O → C`, injective on objects, from the translation groupoid of an M-polyfold `O`
with an action of a finite group `G` by sc-smooth maps. -/
structure Uniformizer (C : GroupoidalCategory.{u}) : Type (u + 1) where
  /-- The M-polyfold `O`. -/
  O : Type u
  [topO : TopologicalSpace O]
  [t2O : T2Space O]
  [paraO : ParacompactSpace O]
  /-- The M-polyfold structure of `O`. -/
  P : MPolyfold O
  /-- The finite group `G`. -/
  G : Type u
  [grp : Group G]
  [fin : Finite G]
  [topG : TopologicalSpace G]
  [discG : DiscreteTopology G]
  [act : MulAction G O]
  /-- `γ : G → Diff_sc(O)`: every `g ∗ ·` is sc-smooth (with sc-smooth inverse `g⁻¹ ∗ ·`). -/
  smooth_smul : ∀ g : G, P.IsScSmoothMap P fun y => g • y
  /-- The functor `Ψ : G ⋉ O → C`. -/
  functor : GroupoidFunctor (GroupoidStr.translation G O) C.toGroupoidStr
  /-- (2) `Ψ` is injective on objects. -/
  injective_obj : Injective functor.obj
  /-- (2) `Ψ` is full. -/
  full : functor.toFunctor.Full
  /-- (2) `Ψ` is faithful. -/
  faithful : functor.toFunctor.Faithful

attribute [instance] Uniformizer.topO Uniformizer.t2O Uniformizer.paraO Uniformizer.grp
  Uniformizer.fin Uniformizer.topG Uniformizer.discG Uniformizer.act

namespace Uniformizer

variable {C : GroupoidalCategory.{u}} (Ψ : C.Uniformizer)

/-- `Ψ` on objects. -/
abbrev obj : Ψ.O → C.Obj := Ψ.functor.obj

/-- `Ψ` on morphisms, `Ψ(g, q) : Ψ(q) → Ψ(g ∗ q)`. -/
abbrev mor : Ψ.G × Ψ.O → C.Mor := Ψ.functor.mor

@[simp] theorem src_mor (p : Ψ.G × Ψ.O) : C.toGroupoidStr.src (Ψ.mor p) = Ψ.obj p.2 :=
  Ψ.functor.src_mor p

@[simp] theorem tgt_mor (p : Ψ.G × Ψ.O) : C.toGroupoidStr.tgt (Ψ.mor p) = Ψ.obj (p.1 • p.2) :=
  Ψ.functor.tgt_mor p

/-- The translation ep-groupoid `G ⋉ O` of `Ψ` (Definition 17.1.2). -/
def ep : EpGroupoid Ψ.O (Ψ.G × Ψ.O) := EpGroupoid.Examples.actionEpGroupoid Ψ.smooth_smul

theorem ep_toGroupoidStr : Ψ.ep.toGroupoidStr = GroupoidStr.translation Ψ.G Ψ.O := rfl

/-- `Ψ` is **at `α`**: `Ψ(q₀) = α` for some `q₀ ∈ O` (Definition 17.1.3 (2)). -/
def IsAt (α : C.Obj) : Prop := ∃ q, Ψ.obj q = α

/-- `q` is fixed by the whole group `G`. -/
def FixesPoint (q : Ψ.O) : Prop := ∀ g : Ψ.G, g • q = q

/-- `Ψ` is **centred at `α`**: `Ψ(q₀) = α` for a `q₀` fixed by `G` (the reading "`G` is the
isotropy group" of Lemma 17.1.9 and Definition 19.1.2; then `G ≅ Aut(α)`, `isotropyEquiv`). -/
def IsCentredAt (α : C.Obj) : Prop := ∃ q, Ψ.obj q = α ∧ Ψ.FixesPoint q

theorem IsCentredAt.isAt {α : C.Obj} (h : Ψ.IsCentredAt α) : Ψ.IsAt α :=
  let ⟨q, hq, _⟩ := h
  ⟨q, hq⟩

/-! ### Full faithfulness in terms of the structure maps -/

/-- **Fullness**: every `φ : Ψ(q) → Ψ(q')` is `Ψ(g, q)` for some `g` with `g ∗ q = q'`. -/
theorem exists_smul_eq_mor {q q' : Ψ.O} {φ : C.Mor} (hs : C.toGroupoidStr.src φ = Ψ.obj q)
    (ht : C.toGroupoidStr.tgt φ = Ψ.obj q') : ∃ g : Ψ.G, g • q = q' ∧ Ψ.mor (g, q) = φ := by
  obtain ⟨p, hp1, hp2, hp3⟩ := (GroupoidFunctor.full_iff Ψ.functor).1 Ψ.full q q' φ hs ht
  obtain ⟨g, x⟩ := p
  change x = q at hp1
  subst hp1
  exact ⟨g, hp2, hp3⟩

/-- **Faithfulness and injectivity on objects**: `Ψ` is injective on morphisms. -/
theorem mor_injective : Injective Ψ.mor := by
  intro p p' h
  have hs : p.2 = p'.2 := Ψ.injective_obj (by
    have := congrArg C.toGroupoidStr.src h
    rwa [Ψ.src_mor, Ψ.src_mor] at this)
  have ht : p.1 • p.2 = p'.1 • p'.2 := Ψ.injective_obj (by
    have := congrArg C.toGroupoidStr.tgt h
    rwa [Ψ.tgt_mor, Ψ.tgt_mor] at this)
  exact (GroupoidFunctor.faithful_iff Ψ.functor).1 Ψ.faithful p p' hs ht h

theorem mor_eq_mor_iff {g h : Ψ.G} {q : Ψ.O} : Ψ.mor (g, q) = Ψ.mor (h, q) ↔ g = h :=
  ⟨fun e => congrArg Prod.fst (Ψ.mor_injective e), fun e => e ▸ rfl⟩

/-- **For `q` fixed by `G`, `G ≅ Aut(Ψ(q))`**, `g ↦ Ψ(g, q)` (fullness and faithfulness). -/
def isotropyEquiv {q : Ψ.O} (hq : Ψ.FixesPoint q) :
    Ψ.G ≃* C.toGroupoidStr.Isotropy (Ψ.obj q) where
  toFun g := ⟨Ψ.mor (g, q), Ψ.src_mor _, (Ψ.tgt_mor _).trans (congrArg Ψ.obj (hq g))⟩
  invFun k := (Ψ.exists_smul_eq_mor k.src_val k.tgt_val).choose
  left_inv g := by
    have h := (Ψ.exists_smul_eq_mor (φ := Ψ.mor (g, q)) (q' := q) (Ψ.src_mor _)
      ((Ψ.tgt_mor _).trans (congrArg Ψ.obj (hq g)))).choose_spec.2
    exact Ψ.mor_eq_mor_iff.1 h
  right_inv k := GroupoidStr.Isotropy.ext (Ψ.exists_smul_eq_mor k.src_val k.tgt_val).choose_spec.2
  map_mul' g h := GroupoidStr.Isotropy.ext (by
    change Ψ.mor (g * h, q) = C.toGroupoidStr.comp (Ψ.mor (g, q)) (Ψ.mor (h, q))
    have hc : (GroupoidStr.translation Ψ.G Ψ.O).src (g, q) =
        (GroupoidStr.translation Ψ.G Ψ.O).tgt (h, q) := (hq h).symm
    rw [← Ψ.functor.mor_comp _ _ hc]
    rfl)

@[simp]
theorem isotropyEquiv_apply_val {q : Ψ.O} (hq : Ψ.FixesPoint q) (g : Ψ.G) :
    (Ψ.isotropyEquiv hq g).val = Ψ.mor (g, q) := rfl

/-! ### Remark 17.1.4 -/

/-- **2021 Remark 17.1.4, p. 745**: the full subcategory of `C` on the objects `Ψ(O)` is in
bijective functorial correspondence with `G ⋉ O`: `Ψ` corestricts to a functor
`G ⋉ O → C|_{Ψ(O)}` which is bijective on objects and on morphisms.  (`G ⋉ O` is the
ep-groupoid `Ψ.ep`.) -/
theorem remark_17_1_4 :
    ∃ E : GroupoidFunctor (GroupoidStr.translation Ψ.G Ψ.O)
        (C.toGroupoidStr.fullSub (range Ψ.obj)),
      Bijective E.obj ∧ Bijective E.mor ∧ (∀ q, (E.obj q).1 = Ψ.obj q) ∧
        ∀ p, (E.mor p).1 = Ψ.mor p := by
  classical
  let E : GroupoidFunctor (GroupoidStr.translation Ψ.G Ψ.O)
      (C.toGroupoidStr.fullSub (range Ψ.obj)) :=
    { obj := fun q => ⟨Ψ.obj q, q, rfl⟩
      mor := fun p => ⟨Ψ.mor p, by rw [Ψ.src_mor]; exact ⟨_, rfl⟩,
        by rw [Ψ.tgt_mor]; exact ⟨_, rfl⟩⟩
      src_mor := fun p => Subtype.ext (Ψ.src_mor p)
      tgt_mor := fun p => Subtype.ext (Ψ.tgt_mor p)
      mor_comp := fun p p' h => by
        have h' : C.toGroupoidStr.src (Ψ.mor p) = C.toGroupoidStr.tgt (Ψ.mor p') := by
          rw [Ψ.src_mor, Ψ.tgt_mor]
          exact congrArg Ψ.obj h
        apply Subtype.ext
        change Ψ.mor _ = (if h : _ then _ else _ : C.toGroupoidStr.morOn (range Ψ.obj)).1
        rw [dif_pos h']
        exact Ψ.functor.mor_comp p p' h
      mor_unit := fun q => Subtype.ext (Ψ.functor.mor_unit q) }
  refine ⟨E, ⟨fun q q' h => Ψ.injective_obj (congrArg Subtype.val h), ?_⟩,
    ⟨fun p p' h => Ψ.mor_injective (congrArg Subtype.val h), ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · rintro ⟨_, q, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨φ, ⟨q, hq⟩, ⟨q', hq'⟩⟩
    obtain ⟨g, -, hg⟩ := Ψ.exists_smul_eq_mor hq.symm hq'.symm
    exact ⟨(g, q), Subtype.ext hg⟩

/-! ### Transition sets of uniformizers -/

/-- **2021 Definition 17.1.5, p. 745**: the **transition set** `M(Ψ, Ψ')` of two uniformizers,
the tuples `(q, φ, q')` with `φ : Ψ(q) → Ψ'(q')`. -/
abbrev Trans (Ψ Ψ' : C.Uniformizer) : Type u :=
  C.toGroupoidStr.TransitionSet Ψ.obj Ψ'.obj

/-- **The map `Ψ̂` of 2021 Lemma 17.1.9, (17.1), p. 748**: `(g, p) ↦ (p, Ψ(g, p), g ∗ p)`. -/
def hat (p : Ψ.G × Ψ.O) : Ψ.Trans Ψ := ⟨p.2, Ψ.mor p, p.1 • p.2, Ψ.src_mor p, Ψ.tgt_mor p⟩

@[simp] theorem src_hat (p : Ψ.G × Ψ.O) : (Ψ.hat p).src = p.2 := rfl
@[simp] theorem tgt_hat (p : Ψ.G × Ψ.O) : (Ψ.hat p).tgt = p.1 • p.2 := rfl
@[simp] theorem mor_hat (p : Ψ.G × Ψ.O) : (Ψ.hat p).mor = Ψ.mor p := rfl

/-- **2021 Lemma 17.1.9, p. 748, first step of the proof**: `Ψ̂ : G × O → M(Ψ, Ψ)` is a bijection
(injectivity on objects, faithfulness, fullness). -/
theorem hat_bijective : Bijective Ψ.hat := by
  refine ⟨fun p p' h => Ψ.mor_injective (congrArg GroupoidStr.TransitionSet.mor h), fun a => ?_⟩
  obtain ⟨g, hg, hm⟩ := Ψ.exists_smul_eq_mor a.src_mor a.tgt_mor
  exact ⟨(g, a.src), GroupoidStr.TransitionSet.ext rfl hm hg⟩

/-- `Ψ̂` as an equivalence `G × O ≃ M(Ψ, Ψ)`. -/
def hatEquiv : Ψ.G × Ψ.O ≃ Ψ.Trans Ψ := Equiv.ofBijective Ψ.hat Ψ.hat_bijective

@[simp] theorem hatEquiv_apply (p : Ψ.G × Ψ.O) : Ψ.hatEquiv p = Ψ.hat p := rfl

theorem hat_one (q : Ψ.O) : Ψ.hat (1, q) = GroupoidStr.TransitionSet.unit q :=
  GroupoidStr.TransitionSet.ext rfl (Ψ.functor.mor_unit q) (one_smul _ q)

/-! ### The bound on p. 749 -/

variable {Ψ' : C.Uniformizer}

/-- **The elements of `M(Ψ, Ψ')` over a fixed `q` (2021 p. 749)**: given one of them,
`a₀ = (q, φ₀, q'₀)`, they are exactly the `(q, Ψ'(g', q'₀) ∘ φ₀, g' ∗ q'₀)`, `g' ∈ G'`, each
once. -/
def fiberEquiv (a₀ : Ψ.Trans Ψ') : Ψ'.G ≃ {a : Ψ.Trans Ψ' // a.src = a₀.src} where
  toFun g := ⟨GroupoidStr.TransitionSet.comp (Ψ'.hat (g, a₀.tgt)) a₀ (by simp [a₀.tgt_mor]), rfl⟩
  invFun a := (Ψ'.exists_smul_eq_mor
    (φ := C.toGroupoidStr.comp a.1.mor (C.toGroupoidStr.inv a₀.mor))
      (q := a₀.tgt) (q' := a.1.tgt) (by
        rw [C.toGroupoidStr.src_comp _ _ (by rw [C.toGroupoidStr.tgt_inv, a.1.src_mor,
          a₀.src_mor, a.2]), C.toGroupoidStr.src_inv, a₀.tgt_mor])
      (by rw [C.toGroupoidStr.tgt_comp _ _ (by rw [C.toGroupoidStr.tgt_inv, a.1.src_mor,
          a₀.src_mor, a.2]), a.1.tgt_mor])).choose
  left_inv g := by
    set a : {a : Ψ.Trans Ψ' // a.src = a₀.src} :=
      ⟨GroupoidStr.TransitionSet.comp (Ψ'.hat (g, a₀.tgt)) a₀ (by simp [a₀.tgt_mor]), rfl⟩
    have h0 : C.toGroupoidStr.src a.1.mor = C.toGroupoidStr.tgt (C.toGroupoidStr.inv a₀.mor) := by
      rw [C.toGroupoidStr.tgt_inv, a.1.src_mor, a₀.src_mor, a.2]
    have hs := (Ψ'.exists_smul_eq_mor (φ := C.toGroupoidStr.comp a.1.mor
      (C.toGroupoidStr.inv a₀.mor)) (q := a₀.tgt) (q' := a.1.tgt)
      (by rw [C.toGroupoidStr.src_comp _ _ h0, C.toGroupoidStr.src_inv, a₀.tgt_mor])
      (by rw [C.toGroupoidStr.tgt_comp _ _ h0, a.1.tgt_mor])).choose_spec.2
    refine Ψ'.mor_eq_mor_iff.1 (hs.trans ?_)
    change C.toGroupoidStr.comp (C.toGroupoidStr.comp (Ψ'.mor (g, a₀.tgt)) a₀.mor)
      (C.toGroupoidStr.inv a₀.mor) = _
    exact GroupoidStr.comp_inv_cancel_right (by rw [Ψ'.src_mor, a₀.tgt_mor])
  right_inv a := by
    have h0 : C.toGroupoidStr.src a.1.mor = C.toGroupoidStr.tgt (C.toGroupoidStr.inv a₀.mor) := by
      rw [C.toGroupoidStr.tgt_inv, a.1.src_mor, a₀.src_mor, a.2]
    have hs := (Ψ'.exists_smul_eq_mor (φ := C.toGroupoidStr.comp a.1.mor
      (C.toGroupoidStr.inv a₀.mor)) (q := a₀.tgt) (q' := a.1.tgt)
      (by rw [C.toGroupoidStr.src_comp _ _ h0, C.toGroupoidStr.src_inv, a₀.tgt_mor])
      (by rw [C.toGroupoidStr.tgt_comp _ _ h0, a.1.tgt_mor])).choose_spec
    refine Subtype.ext (GroupoidStr.TransitionSet.ext a.2.symm ?_ hs.1)
    change C.toGroupoidStr.comp (Ψ'.mor (_, a₀.tgt)) a₀.mor = a.1.mor
    rw [hs.2, GroupoidStr.comp_assoc _ _ _ _ h0 (by rw [C.toGroupoidStr.src_inv]),
      C.toGroupoidStr.inv_comp, GroupoidStr.comp_unit_of_eq (by rw [a.1.src_mor, a₀.src_mor, a.2])]

/-- The elements of `M(Ψ, Ψ')` over a fixed `q` form a finite set. -/
theorem finite_fiber (q : Ψ.O) : {a : Ψ.Trans Ψ' | a.src = q}.Finite := by
  rcases isEmpty_or_nonempty {a : Ψ.Trans Ψ' // a.src = q} with h | ⟨a₀, rfl⟩
  · convert Set.finite_empty
    exact eq_empty_iff_forall_notMem.2 fun a ha => h.false ⟨a, ha⟩
  · have := Finite.of_equiv _ (Ψ.fiberEquiv a₀)
    exact Set.finite_coe_iff.1 this

/-- When there is an element over `q`, there are exactly `♯G'` of them (2021 p. 749). -/
theorem ncard_fiber_eq (a₀ : Ψ.Trans Ψ') :
    {a : Ψ.Trans Ψ' | a.src = a₀.src}.ncard = Nat.card Ψ'.G := by
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_congr (Ψ.fiberEquiv a₀)).symm

/-- **2021 p. 749**: for fixed `q ∈ O` there are at most `♯G'` elements `(q, φ, p)` of
`M(Ψ, Ψ')`. -/
theorem ncard_fiber_le (q : Ψ.O) : {a : Ψ.Trans Ψ' | a.src = q}.ncard ≤ Nat.card Ψ'.G := by
  rcases isEmpty_or_nonempty {a : Ψ.Trans Ψ' // a.src = q} with h | ⟨a₀, rfl⟩
  · rw [show {a : Ψ.Trans Ψ' | a.src = q} = ∅ from
      eq_empty_iff_forall_notMem.2 fun a ha => h.false ⟨a, ha⟩, ncard_empty]
    exact Nat.zero_le _
  · exact (Ψ.ncard_fiber_eq a₀).le

/-- `q` is the source of an element of `M(Ψ, Ψ')` iff `Ψ(q)` is isomorphic to an object of
`Ψ'(O')`. -/
theorem src_mem_range_iff (q : Ψ.O) :
    q ∈ range (GroupoidStr.TransitionSet.src : Ψ.Trans Ψ' → Ψ.O) ↔
      ∃ q' : Ψ'.O, C.toGroupoidStr.Isomorphic (Ψ.obj q) (Ψ'.obj q') := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.tgt, a.mor, a.src_mor, a.tgt_mor⟩
  · rintro ⟨q', φ, hs, ht⟩
    exact ⟨⟨q, φ, q', hs, ht⟩, rfl⟩

end Uniformizer

end GroupoidalCategory

namespace GCT

/-- **2021 Definition 17.1.3, p. 745**: a **local uniformizer** for the GCT `C`: a uniformizer
`Ψ : G ⋉ O → C` (fully faithful, injective on objects) such that (3) the induced map
`|Ψ| : G\O → |C|` is a homeomorphism onto an open subset of `|C|`.  It is a local uniformizer at
`α` when moreover `Ψ.IsAt α`. -/
structure LocalUniformizer (C : GCT.{u}) : Type (u + 1)
    extends C.toGroupoidalCategory.Uniformizer where
  /-- (3) `|Ψ| : G\O → |C|` is a homeomorphism onto an open subset. -/
  isOpenEmbedding_orbitMap : IsOpenEmbedding functor.orbitMap

namespace LocalUniformizer

variable {C : GCT.{u}} (Ψ : C.LocalUniformizer)

/-- `Ψ` on objects. -/
abbrev obj : Ψ.O → C.Obj := Ψ.functor.obj

/-- `Ψ` is at `α` (Definition 17.1.3 (2)). -/
abbrev IsAt (α : C.Obj) : Prop := Ψ.toUniformizer.IsAt α

/-- The transition set `M(Ψ, Ψ')` (Definition 17.1.5). -/
abbrev Trans (Ψ Ψ' : C.LocalUniformizer) : Type u := Ψ.toUniformizer.Trans Ψ'.toUniformizer

/-- **The footprint** `footprint(Ψ) = |Ψ(O)|` (Definition 17.1.3). -/
def footprint : Set C.toGroupoidStr.OrbitSpace := range Ψ.functor.orbitMap

/-- The footprint is open in `|C|` (Definition 17.1.3). -/
theorem isOpen_footprint : IsOpen Ψ.footprint := Ψ.isOpenEmbedding_orbitMap.isOpen_range

theorem mem_footprint_iff {z : C.toGroupoidStr.OrbitSpace} :
    z ∈ Ψ.footprint ↔ ∃ q, C.toGroupoidStr.π (Ψ.obj q) = z := by
  constructor
  · rintro ⟨w, rfl⟩
    induction w using Quotient.inductionOn with
    | h q => exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(GroupoidStr.translation Ψ.G Ψ.O).π q, rfl⟩

theorem π_obj_mem_footprint (q : Ψ.O) : C.toGroupoidStr.π (Ψ.obj q) ∈ Ψ.footprint :=
  Ψ.mem_footprint_iff.2 ⟨q, rfl⟩

theorem mem_footprint_of_isAt {α : C.Obj} (h : Ψ.IsAt α) : C.toGroupoidStr.π α ∈ Ψ.footprint :=
  let ⟨q, hq⟩ := h
  hq ▸ Ψ.π_obj_mem_footprint q

/-- `q ↦ |Ψ(q)|` is continuous `O → |C|`. -/
theorem continuous_π_obj : Continuous fun q : Ψ.O => C.toGroupoidStr.π (Ψ.obj q) :=
  Ψ.isOpenEmbedding_orbitMap.continuous.comp continuous_quot_mk

/-- `q ↦ |Ψ(q)|` is an open map `O → |C|`. -/
theorem isOpenMap_π_obj : IsOpenMap fun q : Ψ.O => C.toGroupoidStr.π (Ψ.obj q) :=
  Ψ.isOpenEmbedding_orbitMap.isOpenMap.comp (GroupoidStr.isOpenMap_π_translation
    (EpGroupoid.Examples.action_continuous_smul Ψ.smooth_smul))

/-- `Ψ` is **tame** if `O` is tame (Definition 17.1.3). -/
def IsTame : Prop := Ψ.P.IsTame

/-! ### Witnesses -/

section Tautological

variable {G O : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O] {P : MPolyfold O}

theorem orbitMap_id_eq (K V : Type u) [Group K] [MulAction K V] :
    (GroupoidFunctor.id (GroupoidStr.translation K V)).orbitMap = id :=
  funext fun z => Quotient.inductionOn z fun _ => rfl

variable (P) in
/-- **The tautological local uniformizer** of a translation GCT `G ⋉ O`: the identity functor
(a local uniformizer at every object). -/
abbrev tautological (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y) :
    (GCT.translation G O hP).LocalUniformizer where
  O := O
  P := P
  G := G
  smooth_smul := hP
  functor := GroupoidFunctor.id _
  injective_obj := injective_id
  full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => ⟨ψ, hs, ht, rfl⟩
  faithful := (GroupoidFunctor.faithful_iff _).2 fun _ _ _ _ h => h
  isOpenEmbedding_orbitMap := by
    rw [orbitMap_id_eq]
    exact IsOpenEmbedding.id

theorem tautological_isAt (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y) (x : O) :
    (tautological P hP).IsAt x := ⟨x, rfl⟩

theorem tautological_footprint (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y) :
    (tautological P hP).footprint = univ := by
  change range (GroupoidFunctor.id (GroupoidStr.translation G O)).orbitMap = univ
  rw [orbitMap_id_eq, range_id]

end Tautological

/-- **The non-degenerate witness of Definition 17.1.3**: the identity uniformizer of `ℤ/2 ⋉ ℝ`
(`O = ℝ`, `G = ℤ/2` acting by reflection). -/
abbrev reflection : GCT.reflection.LocalUniformizer :=
  tautological _ EpGroupoid.Examples.isScSmoothMap_units_smul

/-- The reflection uniformizer is centred at `0`: `0` is fixed by `G = ℤ/2`, so
`G ≅ Aut(0) = ℤ/2` (`Uniformizer.isotropyEquiv`); `G` acts non-trivially on `O = ℝ`. -/
theorem reflection_isCentredAt :
    reflection.toUniformizer.IsCentredAt (0 : Fin 1 → ℝ) ∧
      ∃ (g : reflection.G) (x : reflection.O), g • x ≠ x :=
  ⟨⟨0, rfl, fun g => smul_zero g⟩, (-1 : ℤˣ), fun _ => 1, fun h => by
    have h' : -(fun _ => 1 : Fin 1 → ℝ) = fun _ => 1 :=
      (EpGroupoid.Examples.units_smul_rn_neg_one _).symm.trans h
    have := congrFun h' 0
    norm_num at this⟩

theorem reflection_isTame : reflection.IsTame := EpGroupoid.Examples.isTame_reflection

end LocalUniformizer

end GCT

end Polyfold
