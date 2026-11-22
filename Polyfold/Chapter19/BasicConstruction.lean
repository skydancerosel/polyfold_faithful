import Polyfold.Chapter17.LocalUniformizer
import Polyfold.Chapter8.TangentLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.1 "The Basic Constructions" (pp. 863–868): **Definition 19.1.1** (groupoidal category),
**Definition 19.1.2** (uniformizer), **Definition 19.1.3** (uniformizer construction),
**Remark 19.1.4**, the transition sets `M(Ψ, Ψ')` with `s, t, u, ι, m` (p. 865), the
**Properties of Transition Data (19.3)** (A)–(F) (pp. 866–867), the restriction of transition data
(p. 867), **Definition 19.1.5** (equivalence), **Definition 19.1.6** (transition construction),
**Definition 19.1.7** (basic construction) and **Remark 19.1.8**.  Numbers and pages are the
2021 text's.

# Basic constructions

## The text, paraphrased

(19.1.1) A groupoidal category: all morphisms invertible, finitely many morphisms between two
objects, a set of isomorphism classes.  (19.1.2) A uniformizer at `α` is a functor
`Ψ : G ⋉ O → S` from the translation groupoid of an M-polyfold `O` with an action of `G` by
sc-diffeomorphisms, injective on objects and fully faithful, with `Ψ(ō) = α` for some `ō`; no
topology is involved.  (19.1.3) A uniformizer construction `F : S⁻ → SET` gives a set `F(α)` of
uniformizers at `α`.  (19.1.4) Often `F` is a functor on `S`: `F(φ) : F(α) → F(α')` is a bijection.
(p. 865) `M(Ψ, Ψ') = {(o, φ, o')}` with `s, t, u, ι, m`.  (pp. 866–867) Transition data `F`
associate to `h = (o, φ, o') ∈ M(Ψ, Ψ')` a map `F_h : (V(o), o) → (M(Ψ, Ψ'), h)`, `V(o)` open,
with `f_h = t ∘ F_h` and (A) `f_h` has open image and is an sc-diffeomorphism onto it,
`s(F_h(q)) = q`, and `F_h(q) = (q, Ψ(g, q), g ∗ q)` if `Ψ = Ψ'`, `h = (o, Ψ(g, o), g ∗ o)`;
(B) `F_{F_h(q)}(p) = F_h(p)` for `q ∈ V(o)`, `p ∈ V(q) ∩ V(o)`; (C) `F_{u(o)}(q) = u(q)`;
(D) `F_{ι(h)}(f_h(q)) = ι(F_h(q))` where `f_h(q) ∈ V(o')`; (E) `f_{h'} ∘ f_h = f_{m(h', h)}` and
`m(F_{h'}(f_h(q)), F_h(q)) = F_{m(h', h)}(q)` on `W(o) ∩ V̂(o)`; (F) for `h₁ ≠ h₂` with the same
source `o`, the images of small neighbourhoods of `o` under `F_{h₁}`, `F_{h₂}` are disjoint.
Shrinking the domains gives transition data again (restriction).  (19.1.5) Two transition data are
equivalent if suitable restrictions coincide.  (19.1.6) A transition construction is an
equivalence class.  (19.1.7) A basic construction is a pair `(F, 𝓕)`.  (19.1.8) After shrinking,
`f_h : V(o) → V(o')` is an sc-diffeomorphism with `F_{ι(h)} ∘ f_h = ι ∘ F_h`; similarly for the
multiplication with three neighbourhoods; (C) and the special form of (A); (B) says `F_{h*} = F_h`
near `s(h)` for `h*` near `h`; all this persists on smaller neighbourhoods.

## What is formalized (namespace `Polyfold.GroupoidalCategory`)

* **Definition 19.1.1** is Chapter 17's `GroupoidalCategory` (the same notion as Definition
  17.1.1 (1)–(3)); `definition_19_1_1` spells out (1)–(2).
* **Definition 19.1.2** is Chapter 17's `GroupoidalCategory.Uniformizer` (no topology on `|C|`)
  with the predicate `Uniformizer.IsAt α` ((3)); the transition set `M(Ψ, Ψ')` is
  `Uniformizer.Trans` (Chapter 17, `GroupoidStr.TransitionSet`) with its maps `src`, `tgt`,
  `TransitionSet.unit`, `inv`, `comp`/`mul`.
* `UniformizerConstruction C` (**Definition 19.1.3**), `Unif`, the predicates `HasUniformizers`
  (`F(α) ≠ ∅` for all `α`), `HasClassUniformizers` (every isomorphism class contains an `α` with
  `F(α) ≠ ∅`), `IsCentred`; `UniformizerConstruction.Functorial` and `remark_19_1_4`.
* `TransitionData U` (**Properties (19.3) (A)–(F)**, pp. 866–867): fields `dom` (`V(o)`), `map`
  (`F_h`), `isOpen_dom`, `mem_dom`, `map_src` (`F_h(o) = h`), (A) `src_map`, `diffeo`,
  `map_hat`; (B) `stability`; (C) `identity`; (D) `inversion`; (E) `multiplication`;
  (F) `hausdorff`.  `fmap` (`f_h`), `fmap_src`, `continuousOn_fmap`, `mul_fmap` (the first identity
  of (E)), `exists_nbhd_fmap`, `isScDiffeoOn_fmap_restrict`.
* `TransitionData.restrict` (the restriction of p. 867 is again transition data),
  `TransitionData.Equiv` and `TransitionData.setoid` (**Definition 19.1.5**),
  `equiv_restrict`, `TransitionConstruction` (**Definition 19.1.6**), `BasicConstruction`
  (**Definition 19.1.7**).
* **Remark 19.1.8**: `remark_19_1_8_inv`, `remark_19_1_8_hat`, `remark_19_1_8_unit`,
  `remark_19_1_8_mul`, `remark_19_1_8_stability`.

## Readings

* Definition 19.1.2 opens with "`α` an object with isotropy group `G`" and asks in (3) only
  `Ψ(ō) = α`.  We formalize (1)–(3) as printed (`IsAt α`).  The stronger reading `G = Aut(α)`
  (`G` fixes `ō`, Chapter 17's `IsCentredAt`) is the predicate `UniformizerConstruction.IsCentred`;
  no result of §§19.1–19.3 uses it, so the results are stated for the weaker definition and
  cover the stronger one.
* `F : S⁻ → SET` is a function from objects to sets of uniformizers (`S⁻` has only identities).
* The transition data are indexed by pairs of members of `F` (`Unif`), as `Ψ ∈ F(α)`,
  `Ψ' ∈ F(α')` in the text.  `F_h` is a map on all of `O` whose values matter on `dom h = V(o)`;
  "`F_h : (V(o), o) → (M(Ψ, Ψ'), h)`" includes `F_h(o) = h` (`map_src`).
* (A) "`f_h` has an open image and is an sc-diffeomorphism onto its image" is
  `∃ g, IsScDiffeoOn f_h g V(o) (f_h(V(o)))` (Part I's sc-diffeomorphism between open sets; the
  target is open by definition).
* (D) is required where `f_h(q) ∈ V(o')`, `V(o') = dom ι(h)`; (E) on `W(o) ∩ V̂(o)`,
  `W(o) = V(o) ∩ f_h⁻¹(V(o'))`, `V̂(o) = dom m(h', h)`.  `m` is `TransitionSet.comp` (equal to
  `TransitionSet.mul` on the fibred product, `mul_eq_comp`).  Of the two identities of (E) we
  require the second; the first follows (`mul_fmap`), as `t ∘ m = t ∘ pr₁`.
* (F) "the images of small neighbourhoods are disjoint": an open `V ∋ o` inside both domains with
  `F_{h₁}(V) ∩ F_{h₂}(V) = ∅`.
* Definition 19.1.5 "a choice of smaller open neighbourhoods so that the restrictions coincide"
  is read per `h`: an open `V ∋ s(h)` in both domains on which `F_h = F'_h` (a choice over all `h`
  is then given by choice).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

/-- **2021 Definition 19.1.1, p. 863**: in a groupoidal category (Chapter 17's
`GroupoidalCategory`) (1) every morphism is an isomorphism and (2) between two objects there are
finitely many morphisms; (3) the isomorphism classes form the type `C.OrbitSpace`. -/
theorem definition_19_1_1 (C : GroupoidalCategory.{u}) :
    (∀ φ : C.Mor, C.toGroupoidStr.comp φ (C.toGroupoidStr.inv φ) =
        C.toGroupoidStr.unit (C.toGroupoidStr.tgt φ) ∧
      C.toGroupoidStr.comp (C.toGroupoidStr.inv φ) φ =
        C.toGroupoidStr.unit (C.toGroupoidStr.src φ)) ∧
      ∀ α β : C.Obj, (C.toGroupoidStr.mor α β).Finite :=
  ⟨fun φ => ⟨C.toGroupoidStr.comp_inv φ, C.toGroupoidStr.inv_comp φ⟩, C.finite_mor⟩

variable (C : GroupoidalCategory.{u})

/-- **2021 Definition 19.1.3, p. 865**: a **uniformizer construction** `F : S⁻ → SET` for the
groupoidal category `C`: a set `F(α)` of uniformizers at `α` (Definition 19.1.2) for every
object `α`. -/
structure UniformizerConstruction : Type (u + 1) where
  /-- The sets `F(α)`. -/
  F : C.Obj → Set C.Uniformizer
  /-- Every `Ψ ∈ F(α)` is a uniformizer at `α` (Definition 19.1.2 (3)). -/
  isAt : ∀ α, ∀ Ψ ∈ F α, Ψ.IsAt α

variable {C}

namespace UniformizerConstruction

variable (U : C.UniformizerConstruction)

/-- The uniformizers occurring in `F`. -/
abbrev Unif : Type (u + 1) := {Ψ : C.Uniformizer // ∃ α, Ψ ∈ U.F α}

/-- Every object has a uniformizer: `F(α) ≠ ∅` for all `α` (not part of Definition 19.1.3). -/
def HasUniformizers : Prop := ∀ α, (U.F α).Nonempty

/-- **Every isomorphism class meets a uniformizer**: every class `z ∈ |C|` contains an object
`α` with `F(α) ≠ ∅` (not part of Definition 19.1.3; it is what Theorem 19.2.2 needs). -/
def HasClassUniformizers : Prop := ∀ z : C.OrbitSpace, ∃ α, C.π α = z ∧ (U.F α).Nonempty

theorem HasUniformizers.hasClassUniformizers {U : C.UniformizerConstruction}
    (h : U.HasUniformizers) : U.HasClassUniformizers := fun z =>
  Quotient.inductionOn z fun α => ⟨α, rfl, h α⟩

/-- The reading "`G` is the isotropy group of `α`" of Definition 19.1.2: every `Ψ ∈ F(α)` is
centred at `α` (`Ψ(ō) = α` with `ō` fixed by `G`, so `G ≅ Aut(α)`). -/
def IsCentred : Prop := ∀ α, ∀ Ψ ∈ U.F α, Ψ.IsCentredAt α

/-- **2021 Remark 19.1.4, p. 865**: `F` is a functor on `S`: maps `F(φ) : F(α) → F(α')` for
`φ : α → α'`, with `F(1_α) = id` and `F(φ' ∘ φ) = F(φ') ∘ F(φ)`. -/
structure Functorial where
  /-- `F(φ)`. -/
  map : C.Mor → C.Uniformizer → C.Uniformizer
  mapsTo : ∀ φ, MapsTo (map φ) (U.F (C.toGroupoidStr.src φ)) (U.F (C.toGroupoidStr.tgt φ))
  map_unit : ∀ α, ∀ Ψ ∈ U.F α, map (C.toGroupoidStr.unit α) Ψ = Ψ
  map_comp : ∀ φ' φ, C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ →
    ∀ Ψ ∈ U.F (C.toGroupoidStr.src φ), map (C.toGroupoidStr.comp φ' φ) Ψ = map φ' (map φ Ψ)

/-- **2021 Remark 19.1.4, p. 865**: for a functorial uniformizer construction every
`F(φ) : F(α) → F(α')` is a bijection (with inverse `F(φ⁻¹)`). -/
theorem remark_19_1_4 (T : U.Functorial) (φ : C.Mor) :
    BijOn (T.map φ) (U.F (C.toGroupoidStr.src φ)) (U.F (C.toGroupoidStr.tgt φ)) := by
  set G := C.toGroupoidStr
  have hmi : MapsTo (T.map (G.inv φ)) (U.F (G.tgt φ)) (U.F (G.src φ)) := by
    have := T.mapsTo (G.inv φ)
    rwa [G.src_inv, G.tgt_inv] at this
  refine InvOn.bijOn ⟨fun Ψ hΨ => ?_, fun Ψ hΨ => ?_⟩ (T.mapsTo φ) hmi
  · rw [← T.map_comp _ _ (G.src_inv φ) Ψ hΨ, G.inv_comp, T.map_unit _ Ψ hΨ]
  · have hΨ' : Ψ ∈ U.F (G.src (G.inv φ)) := by rwa [G.src_inv]
    rw [← T.map_comp _ _ (G.tgt_inv φ).symm Ψ hΨ', G.comp_inv, T.map_unit _ Ψ hΨ]

/-! ### Transition data: the Properties (19.3) -/

open GroupoidStr (TransitionSet) in
/-- **2021 Properties of Transition Data (19.3), pp. 865–867**: **transition data** `F` for the
uniformizer construction `F`: for `Ψ, Ψ'` in `F` and `h = (o, φ, o') ∈ M(Ψ, Ψ')` an open
neighbourhood `V(o) = dom h` and a map `F_h : (V(o), o) → (M(Ψ, Ψ'), h)`, `f_h = t ∘ F_h`, with
the Diffeomorphism (A), Stability (B), Identity (C), Inversion (D), Multiplication (E) and
`M`-Hausdorff (F) properties. -/
structure TransitionData where
  /-- The open neighbourhood `V(o)` of `o = s(h)` on which `F_h` is defined. -/
  dom : ∀ (Ψ Ψ' : U.Unif), Ψ.1.Trans Ψ'.1 → Set Ψ.1.O
  /-- The map `F_h` (its values matter on `dom h`). -/
  map : ∀ (Ψ Ψ' : U.Unif), Ψ.1.Trans Ψ'.1 → Ψ.1.O → Ψ.1.Trans Ψ'.1
  isOpen_dom : ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1), IsOpen (dom Ψ Ψ' h)
  mem_dom : ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1), h.src ∈ dom Ψ Ψ' h
  /-- `F_h : (V(o), o) → (M(Ψ, Ψ'), h)` is pointed: `F_h(o) = h`. -/
  map_src : ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1), map Ψ Ψ' h h.src = h
  /-- (A) `s(F_h(q)) = q` for `q ∈ V(o)`. -/
  src_map : ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1), ∀ q ∈ dom Ψ Ψ' h, (map Ψ Ψ' h q).src = q
  /-- (A) `f_h = t ∘ F_h` has an open image and is an sc-diffeomorphism onto it. -/
  diffeo : ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1), ∃ g : Ψ'.1.O → Ψ.1.O,
    Ψ.1.P.IsScDiffeoOn Ψ'.1.P (fun q => (map Ψ Ψ' h q).tgt) g (dom Ψ Ψ' h)
      ((fun q => (map Ψ Ψ' h q).tgt) '' dom Ψ Ψ' h)
  /-- (A) For `Ψ = Ψ'` and `h = (o, Ψ(g, o), g ∗ o)`: `F_h(q) = (q, Ψ(g, q), g ∗ q)`. -/
  map_hat : ∀ (Ψ : U.Unif) (p : Ψ.1.G × Ψ.1.O), ∀ q ∈ dom Ψ Ψ (Ψ.1.hat p),
    map Ψ Ψ (Ψ.1.hat p) q = Ψ.1.hat (p.1, q)
  /-- (B) `F_{F_h(q)}(p) = F_h(p)` for `q ∈ V(o)` and `p ∈ V(q) ∩ V(o)`. -/
  stability : ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1), ∀ q ∈ dom Ψ Ψ' h,
    ∀ p ∈ dom Ψ Ψ' (map Ψ Ψ' h q) ∩ dom Ψ Ψ' h, map Ψ Ψ' (map Ψ Ψ' h q) p = map Ψ Ψ' h p
  /-- (C) `F_{u(o)}(q) = u(q)` for `q ∈ V(o)`. -/
  identity : ∀ (Ψ : U.Unif) (o : Ψ.1.O),
    ∀ q ∈ dom Ψ Ψ (TransitionSet.unit o : Ψ.1.Trans Ψ.1),
      map Ψ Ψ (TransitionSet.unit o) q = TransitionSet.unit q
  /-- (D) `F_{ι(h)}(f_h(q)) = ι(F_h(q))` for `q ∈ V(o)` with `f_h(q) ∈ V(o')`. -/
  inversion : ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1), ∀ q ∈ dom Ψ Ψ' h,
    (map Ψ Ψ' h q).tgt ∈ dom Ψ' Ψ h.inv → map Ψ' Ψ h.inv (map Ψ Ψ' h q).tgt = (map Ψ Ψ' h q).inv
  /-- (E) `m(F_{h'}(f_h(q)), F_h(q)) = F_{m(h', h)}(q)` for `q ∈ W(o) ∩ V̂(o)`. -/
  multiplication : ∀ (Ψ Ψ' Ψ'' : U.Unif) (h : Ψ.1.Trans Ψ'.1) (h' : Ψ'.1.Trans Ψ''.1)
      (hh : h'.src = h.tgt),
    ∀ q (_ : q ∈ dom Ψ Ψ' h) (hq' : (map Ψ Ψ' h q).tgt ∈ dom Ψ' Ψ'' h'),
      q ∈ dom Ψ Ψ'' (TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh)) →
      TransitionSet.comp (map Ψ' Ψ'' h' (map Ψ Ψ' h q).tgt) (map Ψ Ψ' h q)
          (TransitionSet.mor_composable_of_src_eq_tgt (src_map Ψ' Ψ'' h' _ hq')) =
        map Ψ Ψ'' (TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh)) q
  /-- (F) For `h₁ ≠ h₂` with the same source `o`, the images of a small neighbourhood of `o` are
  disjoint. -/
  hausdorff : ∀ (Ψ Ψ' : U.Unif) (h₁ h₂ : Ψ.1.Trans Ψ'.1), h₁ ≠ h₂ → h₁.src = h₂.src →
    ∃ V : Set Ψ.1.O, IsOpen V ∧ h₁.src ∈ V ∧ V ⊆ dom Ψ Ψ' h₁ ∩ dom Ψ Ψ' h₂ ∧
      Disjoint (map Ψ Ψ' h₁ '' V) (map Ψ Ψ' h₂ '' V)

namespace TransitionData

open GroupoidStr (TransitionSet)
open GroupoidStr.TransitionSet (src_inv tgt_comp)

variable {U} (F : U.TransitionData)

/-- `f_h = t ∘ F_h : (V(o), o) → (O', o')` ((19.2)). -/
def fmap (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) (q : Ψ.1.O) : Ψ'.1.O := (F.map Ψ Ψ' h q).tgt

theorem fmap_src (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) : F.fmap Ψ Ψ' h h.src = h.tgt := by
  rw [fmap, F.map_src]

theorem continuousOn_fmap (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) :
    ContinuousOn (F.fmap Ψ Ψ' h) (F.dom Ψ Ψ' h) :=
  (F.diffeo Ψ Ψ' h).choose_spec.isScSmoothOn.continuousOn

theorem isOpen_image_fmap (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) {V : Set Ψ.1.O} (hV : IsOpen V)
    (hsub : V ⊆ F.dom Ψ Ψ' h) : IsOpen (F.fmap Ψ Ψ' h '' V) := by
  obtain ⟨g, hg⟩ := F.diffeo Ψ Ψ' h
  have h' := hg.restrict hV hsub
  change IsOpen ((fun q => (F.map Ψ Ψ' h q).tgt) '' V)
  rw [h'.image_eq]
  exact h'.isOpen_target

/-- (A) on a smaller open set: `f_h : V → f_h(V)` is an sc-diffeomorphism onto an open set. -/
theorem isScDiffeoOn_fmap_restrict (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) {V : Set Ψ.1.O}
    (hV : IsOpen V) (hsub : V ⊆ F.dom Ψ Ψ' h) :
    ∃ g : Ψ'.1.O → Ψ.1.O, Ψ.1.P.IsScDiffeoOn Ψ'.1.P (F.fmap Ψ Ψ' h) g V (F.fmap Ψ Ψ' h '' V) := by
  obtain ⟨g, hg⟩ := F.diffeo Ψ Ψ' h
  have h' := hg.restrict hV hsub
  have e := h'.image_eq
  rw [← e] at h'
  exact ⟨g, h'⟩

/-- The morphism carried by `F_h(q)` relates `Ψ(q)` and `Ψ'(f_h(q))`: `|Ψ(q)| = |Ψ'(f_h(q))|`. -/
theorem π_obj_eq (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) {q : Ψ.1.O} (hq : q ∈ F.dom Ψ Ψ' h) :
    C.π (Ψ.1.obj q) = C.π (Ψ'.1.obj (F.fmap Ψ Ψ' h q)) := by
  refine (C.π_eq_π_iff).2 ⟨(F.map Ψ Ψ' h q).mor, ?_, (F.map Ψ Ψ' h q).tgt_mor⟩
  rw [(F.map Ψ Ψ' h q).src_mor, F.src_map Ψ Ψ' h q hq]

/-- **The step used throughout §19.2**: for `h ∈ M(Ψ, Ψ')` and an open `V' ∋ t(h)` there is an
open `N ∋ s(h)` inside `V(o)` with `f_h(N) ⊂ V'` (continuity of `f_h` at `o`, `f_h(o) = o'`). -/
theorem exists_nbhd_fmap (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) {V' : Set Ψ'.1.O} (hV' : IsOpen V')
    (hh : h.tgt ∈ V') :
    ∃ N : Set Ψ.1.O, IsOpen N ∧ h.src ∈ N ∧ N ⊆ F.dom Ψ Ψ' h ∧ ∀ q ∈ N, F.fmap Ψ Ψ' h q ∈ V' := by
  refine ⟨F.dom Ψ Ψ' h ∩ F.fmap Ψ Ψ' h ⁻¹' V',
    (F.continuousOn_fmap Ψ Ψ' h).isOpen_inter_preimage (F.isOpen_dom Ψ Ψ' h) hV',
    ⟨F.mem_dom Ψ Ψ' h, ?_⟩, inter_subset_left, fun q hq => hq.2⟩
  rw [mem_preimage, F.fmap_src]
  exact hh

/-- **The first identity of (E)**, `f_{h'} ∘ f_h = f_{m(h', h)}` on `W(o) ∩ V̂(o)`, follows from
the second (`t ∘ m = t ∘ pr₁`). -/
theorem mul_fmap {Ψ Ψ' Ψ'' : U.Unif} (h : Ψ.1.Trans Ψ'.1) (h' : Ψ'.1.Trans Ψ''.1)
    (hh : h'.src = h.tgt) {q : Ψ.1.O} (hq : q ∈ F.dom Ψ Ψ' h)
    (hq' : F.fmap Ψ Ψ' h q ∈ F.dom Ψ' Ψ'' h')
    (hm : q ∈ F.dom Ψ Ψ''
      (TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh))) :
    F.fmap Ψ' Ψ'' h' (F.fmap Ψ Ψ' h q) =
      F.fmap Ψ Ψ'' (TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh)) q := by
  unfold fmap
  rw [← F.multiplication Ψ Ψ' Ψ'' h h' hh q hq hq' hm, tgt_comp]

/-! ### Restriction (p. 867) and Definition 19.1.5 -/

/-- **Restriction (p. 867)**: replacing every `V(o)` by a smaller open neighbourhood `Q(o)`
gives again transition data. -/
def restrict (Q : ∀ (Ψ Ψ' : U.Unif), Ψ.1.Trans Ψ'.1 → Set Ψ.1.O)
    (hQo : ∀ (Ψ Ψ' : U.Unif) h, IsOpen (Q Ψ Ψ' h))
    (hQm : ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1), h.src ∈ Q Ψ Ψ' h)
    (hQs : ∀ (Ψ Ψ' : U.Unif) h, Q Ψ Ψ' h ⊆ F.dom Ψ Ψ' h) : U.TransitionData where
  dom := Q
  map := F.map
  isOpen_dom := hQo
  mem_dom := hQm
  map_src := F.map_src
  src_map Ψ Ψ' h q hq := F.src_map Ψ Ψ' h q (hQs _ _ _ hq)
  diffeo Ψ Ψ' h := F.isScDiffeoOn_fmap_restrict Ψ Ψ' h (hQo _ _ _) (hQs _ _ _)
  map_hat Ψ p q hq := F.map_hat Ψ p q (hQs _ _ _ hq)
  stability Ψ Ψ' h q hq p hp :=
    F.stability Ψ Ψ' h q (hQs _ _ _ hq) p ⟨hQs _ _ _ hp.1, hQs _ _ _ hp.2⟩
  identity Ψ o q hq := F.identity Ψ o q (hQs _ _ _ hq)
  inversion Ψ Ψ' h q hq hq' := F.inversion Ψ Ψ' h q (hQs _ _ _ hq) (hQs _ _ _ hq')
  multiplication Ψ Ψ' Ψ'' h h' hh q hq hq' hm :=
    F.multiplication Ψ Ψ' Ψ'' h h' hh q (hQs _ _ _ hq) (hQs _ _ _ hq') (hQs _ _ _ hm)
  hausdorff Ψ Ψ' h₁ h₂ hne hs := by
    obtain ⟨V, hV, hoV, -, hdisj⟩ := F.hausdorff Ψ Ψ' h₁ h₂ hne hs
    refine ⟨V ∩ Q Ψ Ψ' h₁ ∩ Q Ψ Ψ' h₂, (hV.inter (hQo _ _ _)).inter (hQo _ _ _),
      ⟨⟨hoV, hQm _ _ _⟩, hs ▸ hQm _ _ _⟩, fun q hq => ⟨hq.1.2, hq.2⟩, ?_⟩
    exact hdisj.mono (image_mono fun q hq => hq.1.1) (image_mono fun q hq => hq.1.1)

/-- **2021 Definition 19.1.5, p. 867**: transition data `F`, `F'` are **equivalent** if their
restrictions to suitable smaller open neighbourhoods coincide: for every `h` there is an open
`V ∋ s(h)` inside both domains on which `F_h = F'_h`. -/
def Equiv (F F' : U.TransitionData) : Prop :=
  ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1), ∃ V : Set Ψ.1.O, IsOpen V ∧ h.src ∈ V ∧
    V ⊆ F.dom Ψ Ψ' h ∩ F'.dom Ψ Ψ' h ∧ EqOn (F.map Ψ Ψ' h) (F'.map Ψ Ψ' h) V

theorem equiv_refl : F.Equiv F := fun Ψ Ψ' h =>
  ⟨F.dom Ψ Ψ' h, F.isOpen_dom Ψ Ψ' h, F.mem_dom Ψ Ψ' h, fun _ hq => ⟨hq, hq⟩, fun _ _ => rfl⟩

theorem Equiv.symm {F F' : U.TransitionData} (e : F.Equiv F') : F'.Equiv F := fun Ψ Ψ' h => by
  obtain ⟨V, hV, ho, hs, he⟩ := e Ψ Ψ' h
  exact ⟨V, hV, ho, fun _ hq => ⟨(hs hq).2, (hs hq).1⟩, he.symm⟩

theorem Equiv.trans {F F' F'' : U.TransitionData} (e : F.Equiv F') (e' : F'.Equiv F'') :
    F.Equiv F'' := fun Ψ Ψ' h => by
  obtain ⟨V, hV, ho, hs, he⟩ := e Ψ Ψ' h
  obtain ⟨V', hV', ho', hs', he'⟩ := e' Ψ Ψ' h
  exact ⟨V ∩ V', hV.inter hV', ⟨ho, ho'⟩, fun _ hq => ⟨(hs hq.1).1, (hs' hq.2).2⟩,
    fun q hq => (he hq.1).trans (he' hq.2)⟩

variable (U) in
/-- The equivalence relation of Definition 19.1.5. -/
def setoid : Setoid U.TransitionData where
  r := Equiv
  iseqv := ⟨equiv_refl, Equiv.symm, Equiv.trans⟩

/-- A restriction is equivalent to the original transition data (p. 867: "`F'` is for our
purposes as good as `F`"). -/
theorem equiv_restrict (Q : ∀ (Ψ Ψ' : U.Unif), Ψ.1.Trans Ψ'.1 → Set Ψ.1.O)
    (hQo : ∀ (Ψ Ψ' : U.Unif) h, IsOpen (Q Ψ Ψ' h))
    (hQm : ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1), h.src ∈ Q Ψ Ψ' h)
    (hQs : ∀ (Ψ Ψ' : U.Unif) h, Q Ψ Ψ' h ⊆ F.dom Ψ Ψ' h) : F.Equiv (F.restrict Q hQo hQm hQs) :=
  fun Ψ Ψ' h => ⟨Q Ψ Ψ' h, hQo _ _ _, hQm _ _ _, fun _ hq => ⟨hQs _ _ _ hq, hq⟩, fun _ _ => rfl⟩

/-! ### Remark 19.1.8 -/

/-- **2021 Remark 19.1.8, p. 868, (A) and (D)**: for `h = (o, φ, o')` there are open
neighbourhoods `V(o)`, `V(o')` with `f_h : V(o) → V(o')` an sc-diffeomorphism and
`F_{ι(h)}(f_h(q)) = ι(F_h(q))` for `q ∈ V(o)`. -/
theorem remark_19_1_8_inv (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) :
    ∃ (V : Set Ψ.1.O) (V' : Set Ψ'.1.O), IsOpen V ∧ h.src ∈ V ∧ V ⊆ F.dom Ψ Ψ' h ∧
      IsOpen V' ∧ h.tgt ∈ V' ∧
      (∃ g : Ψ'.1.O → Ψ.1.O, Ψ.1.P.IsScDiffeoOn Ψ'.1.P (F.fmap Ψ Ψ' h) g V V') ∧
      ∀ q ∈ V, F.map Ψ' Ψ h.inv (F.fmap Ψ Ψ' h q) = (F.map Ψ Ψ' h q).inv := by
  obtain ⟨N, hN, hoN, hNs, hNf⟩ := F.exists_nbhd_fmap Ψ Ψ' h (F.isOpen_dom Ψ' Ψ h.inv)
    (by simpa only [src_inv] using F.mem_dom Ψ' Ψ h.inv)
  refine ⟨N, F.fmap Ψ Ψ' h '' N, hN, hoN, hNs, F.isOpen_image_fmap Ψ Ψ' h hN hNs,
    ⟨h.src, hoN, F.fmap_src Ψ Ψ' h⟩, F.isScDiffeoOn_fmap_restrict Ψ Ψ' h hN hNs,
    fun q hq => F.inversion Ψ Ψ' h q (hNs hq) (hNf q hq)⟩

/-- **2021 Remark 19.1.8, p. 868, the special form of (A)**: for `Ψ = Ψ'` and
`h = (o, Ψ(g, o), g ∗ o)`, on an open `V(o)`: `f_h(q) = g ∗ q` and
`F_h(q) = (q, Ψ(g, q), g ∗ q)`. -/
theorem remark_19_1_8_hat (Ψ : U.Unif) (p : Ψ.1.G × Ψ.1.O) :
    ∃ V : Set Ψ.1.O, IsOpen V ∧ p.2 ∈ V ∧ ∀ q ∈ V,
      F.fmap Ψ Ψ (Ψ.1.hat p) q = p.1 • q ∧ F.map Ψ Ψ (Ψ.1.hat p) q = Ψ.1.hat (p.1, q) :=
  ⟨F.dom Ψ Ψ (Ψ.1.hat p), F.isOpen_dom _ _ _, F.mem_dom _ _ _, fun q hq => by
    refine ⟨?_, F.map_hat Ψ p q hq⟩
    rw [fmap, F.map_hat Ψ p q hq]
    rfl⟩

/-- **2021 Remark 19.1.8, p. 868, (C)**: there is an open `V(o)` with `F_{u(o)}(q) = u(q)` for
`q ∈ V(o)`. -/
theorem remark_19_1_8_unit (Ψ : U.Unif) (o : Ψ.1.O) :
    ∃ V : Set Ψ.1.O, IsOpen V ∧ o ∈ V ∧
      ∀ q ∈ V, F.map Ψ Ψ (TransitionSet.unit o : Ψ.1.Trans Ψ.1) q = TransitionSet.unit q :=
  ⟨_, F.isOpen_dom _ _ _, F.mem_dom Ψ Ψ (TransitionSet.unit o : Ψ.1.Trans Ψ.1), F.identity Ψ o⟩

/-- **2021 Remark 19.1.8, p. 868, (E)**: for `h = (o, φ, o')`, `h' = (o', φ', o'')` there are open
`V(o)`, `V(o')`, `V(o'')` with `f_h : V(o) → V(o')` and `f_{h'} : V(o') → V(o'')`
sc-diffeomorphisms, `f_{h'} ∘ f_h = f_{m(h', h)}` and `m(F_{h'}(f_h(q)), F_h(q)) = F_{m(h', h)}(q)`
on `V(o)`. -/
theorem remark_19_1_8_mul {Ψ Ψ' Ψ'' : U.Unif} (h : Ψ.1.Trans Ψ'.1) (h' : Ψ'.1.Trans Ψ''.1)
    (hh : h'.src = h.tgt) :
    ∃ (V : Set Ψ.1.O) (V' : Set Ψ'.1.O) (V'' : Set Ψ''.1.O),
      IsOpen V ∧ IsOpen V' ∧ IsOpen V'' ∧ h.src ∈ V ∧ h.tgt ∈ V' ∧ h'.tgt ∈ V'' ∧
      (∃ g, Ψ.1.P.IsScDiffeoOn Ψ'.1.P (F.fmap Ψ Ψ' h) g V V') ∧
      (∃ g', Ψ'.1.P.IsScDiffeoOn Ψ''.1.P (F.fmap Ψ' Ψ'' h') g' V' V'') ∧
      ∀ q (_ : q ∈ V), ∃ (_ : q ∈ F.dom Ψ Ψ' h) (hq₂ : F.fmap Ψ Ψ' h q ∈ F.dom Ψ' Ψ'' h'),
        F.fmap Ψ' Ψ'' h' (F.fmap Ψ Ψ' h q) =
          F.fmap Ψ Ψ'' (TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh)) q ∧
        TransitionSet.comp (F.map Ψ' Ψ'' h' (F.fmap Ψ Ψ' h q)) (F.map Ψ Ψ' h q)
            (TransitionSet.mor_composable_of_src_eq_tgt (F.src_map Ψ' Ψ'' h' _ hq₂)) =
          F.map Ψ Ψ''
            (TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh)) q := by
  set m := TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh)
  obtain ⟨N, hN, hoN, hNs, hNf⟩ := F.exists_nbhd_fmap Ψ Ψ' h (F.isOpen_dom Ψ' Ψ'' h')
    (hh ▸ F.mem_dom Ψ' Ψ'' h')
  have hmo : h.src ∈ F.dom Ψ Ψ'' m := F.mem_dom Ψ Ψ'' m
  set V := N ∩ F.dom Ψ Ψ'' m
  have hV : IsOpen V := hN.inter (F.isOpen_dom _ _ _)
  have hVs : V ⊆ F.dom Ψ Ψ' h := fun q hq => hNs hq.1
  set V' := F.fmap Ψ Ψ' h '' V
  have hV' : IsOpen V' := F.isOpen_image_fmap Ψ Ψ' h hV hVs
  have hV's : V' ⊆ F.dom Ψ' Ψ'' h' := by
    rintro _ ⟨q, hq, rfl⟩
    exact hNf q hq.1
  refine ⟨V, V', F.fmap Ψ' Ψ'' h' '' V', hV, hV', F.isOpen_image_fmap _ _ h' hV' hV's,
    ⟨hoN, hmo⟩, ⟨h.src, ⟨hoN, hmo⟩, F.fmap_src Ψ Ψ' h⟩,
    ⟨h.tgt, ⟨h.src, ⟨hoN, hmo⟩, F.fmap_src Ψ Ψ' h⟩, by rw [← hh, F.fmap_src]⟩,
    F.isScDiffeoOn_fmap_restrict Ψ Ψ' h hV hVs, F.isScDiffeoOn_fmap_restrict Ψ' Ψ'' h' hV' hV's,
    fun q hq => ⟨hVs hq, hNf q hq.1, F.mul_fmap h h' hh (hVs hq) (hNf q hq.1) hq.2,
      F.multiplication Ψ Ψ' Ψ'' h h' hh q (hVs hq) (hNf q hq.1) hq.2⟩⟩

/-- **2021 Remark 19.1.8, p. 868, (B)**: `F_{h*} = F_h` near `s(h*)` for `h* = F_h(q)`, `q` near
`s(h)`. -/
theorem remark_19_1_8_stability (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) {q : Ψ.1.O}
    (hq : q ∈ F.dom Ψ Ψ' h) :
    ∃ N : Set Ψ.1.O, IsOpen N ∧ q ∈ N ∧
      ∀ p ∈ N, F.map Ψ Ψ' (F.map Ψ Ψ' h q) p = F.map Ψ Ψ' h p := by
  refine ⟨F.dom Ψ Ψ' (F.map Ψ Ψ' h q) ∩ F.dom Ψ Ψ' h,
    (F.isOpen_dom _ _ _).inter (F.isOpen_dom _ _ _), ⟨?_, hq⟩,
    fun p hp => F.stability Ψ Ψ' h q hq p hp⟩
  have := F.mem_dom Ψ Ψ' (F.map Ψ Ψ' h q)
  rwa [F.src_map Ψ Ψ' h q hq] at this

end TransitionData

/-- **2021 Definition 19.1.6, p. 867**: a **transition construction** associated to `F`: an
equivalence class of transition data (Definition 19.1.5). -/
def TransitionConstruction : Type (u + 1) := Quotient (TransitionData.setoid U)

end UniformizerConstruction

variable (C) in
/-- **2021 Definition 19.1.7, p. 868**: a **basic construction** `(F, 𝓕)` for the groupoidal
category `C`: a uniformizer construction `F` and an associated transition construction `𝓕`. -/
structure BasicConstruction : Type (u + 1) where
  /-- The uniformizer construction `F`. -/
  U : C.UniformizerConstruction
  /-- The transition construction `𝓕`. -/
  𝓕 : U.TransitionConstruction

namespace BasicConstruction

variable (B : C.BasicConstruction)

/-- A representative `F` of `𝓕` (the text's "we fix a representative `F`"). -/
def rep : B.U.TransitionData := Quotient.out B.𝓕

theorem mk_rep : (⟦B.rep⟧ : B.U.TransitionConstruction) = B.𝓕 := Quotient.out_eq _

end BasicConstruction

end GroupoidalCategory

end Polyfold
