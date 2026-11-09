import Polyfold.Chapter2.Retracts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
Definitions 3.1.1 and 3.1.2 (preprint 3.1 and 3.2): sc-germs of neighbourhoods and sc^k-germs, with the calculus the
proofs of §3.3 use silently (restriction, the chain rule, pairings, linear maps).

# Sc-germs of neighbourhoods and sc^k-germs

## The text, paraphrased

(Definition 3.1.1 (preprint 3.1)) An sc-germ of neighbourhoods around `0 ∈ C`, `O(C, 0)`, is a decreasing sequence
`U₀ ⊃ U₁ ⊃ U₂ ⊃ …` where `U_m` is a relatively open neighbourhood of `0` in `C ∩ E_m`.  Its tangent
`TO(C, 0)` is the sequence `U₁ ⊕ E₀ ⊃ U₂ ⊕ E₁ ⊃ …`.  A relatively open `U ∋ 0` with `U_m = U ∩ E_m`
is an example; "the size of the sets `U_m` does not matter".  (Definition 3.1.2 (preprint 3.2)) An sc⁰-germ
`f : O(C, 0) → F` is a continuous `f : U₀ → F` with `f(U_m) ⊂ F_m`, `f : U_m → F_m` continuous.  An
sc¹-germ is an sc⁰-germ with, for every `x ∈ U₁`, a bounded `Df(x) : E₀ → F₀` with
`|f(x+h) − f(x) − Df(x)h|₀/|h|₁ → 0` (`h ∈ E₁`, `x + h ∈ U₁`), such that
`Tf : TO(C, 0) → TF`, `Tf(x, h) = (f(x), Df(x)h)`, is an sc⁰-germ.  `f` is sc² if `Tf` is sc¹, etc.;
sc-smooth if sc^k for all `k`.

## What is formalized

* `Polyfold.ScNbhdGerm E C` (**Definition 3.1.1 (preprint 3.1)**): `U : ∀ m, Set (E m)`, nested along the
  inclusions, each `U m` of the form `O ∩ C_m` with `O` open and containing `0`;
  `ScNbhdGerm.tangent` (`TO(C, 0)`, with `(TU)_m = U_{m+1} × E_m`), `ScNbhdGerm.ofSet` (the
  example `U_m = U ∩ E_m`), `ScNbhdGerm.full` (the germ of the whole space).
* `Polyfold.IsQuadrantLike E C`: the regularity of `C` the calculus uses (each `C_m` convex with
  nonempty interior, `0 ∈ C`); partial quadrants have it, and it passes to `TC` and to products.
* `Polyfold.IsSc0Germ`, `Polyfold.IsSc1GermWith`, `IsSc1Germ`, `scDerivGerm`, `IsSckGerm`,
  `IsScSmoothGerm` (**Definition 3.1.2 (preprint 3.2)**), the exact analogues of `IsSc0`, `IsSc1With`, …, with
  `U_m` in place of `U ∩ E_m`.
* The bridge `IsSck.isSckGerm`: an sc^k map on a relatively open `U ∋ 0` is an sc^k-germ on
  `ofSet U`.
* The calculus of germs: `IsSckGerm.congr`, `IsSckGerm.mono` (restriction to a smaller germ),
  `IsSckGerm.comp` (the chain rule, Theorem 1.3.1 (preprint 1.21) for germs), `ScOperator.isScSmoothGerm`
  (sc-operators, in particular projections and sc-isomorphisms, are sc-smooth germs),
  `IsSckGerm.pair` (`(f, g)` is sc^k when `f`, `g` are).

## What the text leaves implicit, and the choices made

* A germ of neighbourhoods is *not* re-indexable in general: `(U_{m+1})_m` is not a germ (`U_{m+1}`
  is open in `C_{m+1}`, not in `C_m`).  It is when all levels of `E` coincide (finite-dimensional
  `E`), which is the case for the domain of the solution germ of §3.3.
* Definition 3.1.2 (preprint 3.2) says nothing about composing germs; the proofs of §3.3 compose `Tf` with maps
  built from the solution germ.  The chain rule needs the inner map to send `U_m` into `V_m`
  level by level (`ScNbhdGerm.MapsToGerm`); for the special example this is `f(U) ⊆ V`.
* The derivative `Df(x)` is unique on `U₁` because `U₁ = O ∩ C₁` with `C₁` convex with nonempty
  interior (`IsQuadrantLike`); as in Chapter 1 the tangent map is built from a choice.
* The proofs are those of `ScSmooth.lean`, `ChainRule.lean` with `U ∩ E_m` replaced by `U_m`.
-/

open Set Filter Topology Function Asymptotics

noncomputable section

namespace Polyfold

variable {E F G H : ScBanach}

/-! ### Quadrant-like sets -/

/-- The regularity of `C ⊆ E₀` used by the germ calculus: `0 ∈ C` and every level `C_m` is convex
with nonempty interior.  Partial quadrants have it (`IsPartialQuadrant.isQuadrantLike`). -/
structure IsQuadrantLike (E : ScBanach) (C : Set (E 0)) : Prop where
  zero_mem : (0 : E 0) ∈ C
  convex : ∀ m, Convex ℝ (E.lvlSet C m)
  interior_nonempty : ∀ m, (interior (E.lvlSet C m)).Nonempty

lemma IsPartialQuadrant.isQuadrantLike {C : Set (E 0)} (hC : IsPartialQuadrant E C) :
    IsQuadrantLike E C where
  zero_mem := by
    obtain ⟨n, W, T, rfl⟩ := hC
    show T 0 0 ∈ quadrant n W 0
    rw [map_zero]; intro i; exact le_rfl
  convex := hC.convex_lvlSet
  interior_nonempty := hC.interior_lvlSet_nonempty

lemma isQuadrantLike_univ (E : ScBanach) : IsQuadrantLike E univ where
  zero_mem := mem_univ _
  convex m := by rw [ScBanach.lvlSet_univ]; exact convex_univ
  interior_nonempty m := by rw [ScBanach.lvlSet_univ, interior_univ]; exact univ_nonempty

lemma IsQuadrantLike.tangentSet {C : Set (E 0)} (hC : IsQuadrantLike E C) :
    IsQuadrantLike E.tangent (E.tangentSet C) where
  zero_mem := by
    show (0 : E.tangent 0).1 ∈ E.lvlSet C 1
    simp only [Prod.fst_zero, ScBanach.mem_lvlSet, map_zero]; exact hC.zero_mem
  convex m := by rw [ScBanach.lvlSet_tangentSet]; exact (hC.convex (m + 1)).prod convex_univ
  interior_nonempty m := by
    rw [ScBanach.lvlSet_tangentSet, interior_prod_eq, interior_univ]
    exact (hC.interior_nonempty (m + 1)).prod univ_nonempty

/-- `C̃ × F` in `P ⊕ F` (`P` finite-dimensional with the constant structure) for a convex `C̃ ∋ 0`
with nonempty interior. -/
lemma isQuadrantLike_prod_univ {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {C : Set P} (h0 : (0 : P) ∈ C) (hc : Convex ℝ C)
    (hi : (interior C).Nonempty) (F : ScBanach) :
    IsQuadrantLike ((ScBanach.const P).prod F) (C ×ˢ univ) where
  zero_mem := ⟨h0, mem_univ _⟩
  convex m := by
    have : ((ScBanach.const P).prod F).lvlSet (C ×ˢ univ) m = C ×ˢ univ := by
      ext p; rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase, mem_prod, mem_prod,
        ScBanach.const_toBase]; simp
    rw [this]; exact hc.prod convex_univ
  interior_nonempty m := by
    have : ((ScBanach.const P).prod F).lvlSet (C ×ˢ univ) m = C ×ˢ univ := by
      ext p; rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase, mem_prod, mem_prod,
        ScBanach.const_toBase]; simp
    rw [this, interior_prod_eq, interior_univ]; exact hi.prod univ_nonempty

lemma IsQuadrantLike.uniqueDiffWithinAt {C : Set (E 0)} (hC : IsQuadrantLike E C) {m : ℕ}
    {O : Set (E m)} (hO : IsOpen O) {x : E m} (hx : x ∈ O ∩ E.lvlSet C m) :
    UniqueDiffWithinAt ℝ (O ∩ E.lvlSet C m) x := by
  rw [inter_comm]
  exact (uniqueDiffWithinAt_convex (hC.convex m) (hC.interior_nonempty m)
    (subset_closure hx.2)).inter (hO.mem_nhds hx.1)

/-! ### Definition 3.1.1 (preprint 3.1): sc-germs of neighbourhoods -/

/-- **Definition 3.1.1 (preprint 3.1)**: an **sc-germ of neighbourhoods** `O(C, 0)` around `0 ∈ C`: relatively open
neighbourhoods `U m` of `0` in `C_m ⊆ E_m`, decreasing along the inclusions `E_{m+1} → E_m`. -/
structure ScNbhdGerm (E : ScBanach) (C : Set (E 0)) where
  /-- The level-`m` neighbourhood `U_m ⊆ C_m`. -/
  U : ∀ m, Set (E m)
  nested : ∀ m, ∀ x ∈ U (m + 1), E.incl m x ∈ U m
  zero_mem : ∀ m, (0 : E m) ∈ U m
  relOpen : ∀ m, ∃ O : Set (E m), IsOpen O ∧ U m = O ∩ E.lvlSet C m

namespace ScNbhdGerm

variable {C : Set (E 0)} (G : ScNbhdGerm E C)

lemma U_subset (m : ℕ) : G.U m ⊆ E.lvlSet C m := by
  obtain ⟨O, _, h⟩ := G.relOpen m; rw [h]; exact inter_subset_right

lemma inclK_mem {m k : ℕ} {x : E (m + k)} (hx : x ∈ G.U (m + k)) : E.inclK m k x ∈ G.U m := by
  induction k with
  | zero => exact hx
  | succ k ih => exact ih (G.nested _ x hx)

lemma toBase_mem {m : ℕ} {x : E m} (hx : x ∈ G.U m) : E.toBase m x ∈ G.U 0 := by
  induction m with
  | zero => exact hx
  | succ m ih => exact ih (G.nested m x hx)

lemma shift_toBase_mem {m : ℕ} {x : E (m + 1)} (hx : x ∈ G.U (m + 1)) :
    E.shift.toBase m x ∈ G.U 1 := by
  induction m with
  | zero => exact hx
  | succ m ih => exact ih (G.nested (m + 1) x hx)

lemma uniqueDiffWithinAt (hC : IsQuadrantLike E C) (m : ℕ) {x : E m} (hx : x ∈ G.U m) :
    UniqueDiffWithinAt ℝ (G.U m) x := by
  obtain ⟨O, hO, h⟩ := G.relOpen m
  rw [h] at hx ⊢
  exact hC.uniqueDiffWithinAt hO hx

lemma relOpenConvex (hC : IsQuadrantLike E C) (m : ℕ) :
    ∃ O K : Set (E m), IsOpen O ∧ Convex ℝ K ∧ G.U m = O ∩ K := by
  obtain ⟨O, hO, h⟩ := G.relOpen m
  exact ⟨O, _, hO, hC.convex m, h⟩

/-- The tangent germ `TO(C, 0) = (U_{m+1} ⊕ E_m)_m` (Definition 3.1.1 (preprint 3.1)). -/
def tangent : ScNbhdGerm E.tangent (E.tangentSet C) where
  U m := G.U (m + 1) ×ˢ univ
  nested m p hp := ⟨G.nested (m + 1) p.1 hp.1, mem_univ _⟩
  zero_mem m := ⟨G.zero_mem (m + 1), mem_univ _⟩
  relOpen m := by
    obtain ⟨O, hO, h⟩ := G.relOpen (m + 1)
    refine ⟨O ×ˢ univ, hO.prod isOpen_univ, ?_⟩
    rw [ScBanach.lvlSet_tangentSet, h, prod_inter_prod, univ_inter]

@[simp] lemma tangent_U (m : ℕ) : G.tangent.U m = G.U (m + 1) ×ˢ univ := rfl

lemma mem_tangent_U {m : ℕ} {p : E.tangent m} : p ∈ G.tangent.U m ↔ p.1 ∈ G.U (m + 1) :=
  ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩

/-- The special example of Definition 3.1.1 (preprint 3.1): a relatively open `U ∋ 0` in `C` with
`U_m = U ∩ E_m`. -/
def ofSet {U : Set (E 0)} (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C) (h0 : (0 : E 0) ∈ U) :
    ScNbhdGerm E C where
  U m := E.lvlSet U m
  nested _ _ hx := hx
  zero_mem m := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  relOpen m := by
    obtain ⟨O, hO, rfl⟩ := hU
    exact ⟨E.lvlSet O m, E.isOpen_lvlSet hO m, rfl⟩

@[simp] lemma ofSet_U {U : Set (E 0)} (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C)
    (h0 : (0 : E 0) ∈ U) (m : ℕ) : (ofSet hU h0).U m = E.lvlSet U m := rfl

/-- `TU` is relatively open in `TC` when `U` is relatively open in `C`. -/
lemma tangentSet_relOpen {U : Set (E 0)} (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C) :
    ∃ O : Set (E.tangent 0), IsOpen O ∧ E.tangentSet U = O ∩ E.tangentSet C := by
  obtain ⟨O, hO, rfl⟩ := hU
  refine ⟨E.lvlSet O 1 ×ˢ univ, (E.isOpen_lvlSet hO 1).prod isOpen_univ, ?_⟩
  ext p
  change p.1 ∈ E.lvlSet (O ∩ C) 1 ↔ (p.1 ∈ E.lvlSet O 1 ∧ p.2 ∈ univ) ∧ p.1 ∈ E.lvlSet C 1
  rw [ScBanach.lvlSet_inter]; simp [mem_inter_iff]

lemma zero_mem_tangentSet {U : Set (E 0)} (h0 : (0 : E 0) ∈ U) : (0 : E.tangent 0) ∈ E.tangentSet U := by
  show (0 : E.tangent 0).1 ∈ E.lvlSet U 1
  simp only [Prod.fst_zero, ScBanach.mem_lvlSet, map_zero]; exact h0

lemma ofSet_tangent {U : Set (E 0)} (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C)
    (h0 : (0 : E 0) ∈ U) :
    (ofSet hU h0).tangent = ofSet (tangentSet_relOpen hU) (zero_mem_tangentSet h0) := by
  simp only [tangent, ofSet]
  congr 1
  funext m
  exact (ScBanach.lvlSet_tangentSet E U m).symm

/-- The trivial germ `U_m = E_m` (`C = E`). -/
def full (E : ScBanach) : ScNbhdGerm E Set.univ where
  U _ := Set.univ
  nested _ _ _ := mem_univ _
  zero_mem _ := mem_univ _
  relOpen m := ⟨Set.univ, isOpen_univ, by simp⟩

@[simp] lemma full_U (E : ScBanach) (m : ℕ) : (full E).U m = Set.univ := rfl

/-- `f` maps the germ `G` into the germ `G'` level by level. -/
def MapsToGerm {D : Set (F 0)} (G : ScNbhdGerm E C) (G' : ScNbhdGerm F D) (f : E 0 → F 0) : Prop :=
  ∀ m, MapsTo (levelMap f m) (G.U m) (G'.U m)

lemma mapsToGerm_full (f : E 0 → F 0) : G.MapsToGerm (full F) f := fun _ _ _ => mem_univ _

end ScNbhdGerm

/-! ### Definition 3.1.2 (preprint 3.2): sc⁰-germs -/

variable {C : Set (E 0)} {D : Set (F 0)} {Q : Set (G 0)}

/-- **Definition 3.1.2 (preprint 3.2)**: `f` is an **sc⁰-germ** on `O(C, 0)`: `f(U_m) ⊆ F_m` and `f : U_m → F_m` is
continuous for every `m`. -/
structure IsSc0Germ (G : ScNbhdGerm E C) (f : E 0 → F 0) : Prop where
  mem_range : ∀ m, ∀ x ∈ G.U m, f (E.toBase m x) ∈ range (F.toBase m)
  continuousOn : ∀ m, ContinuousOn (levelMap f m) (G.U m)

namespace IsSc0Germ

variable {G₁ : ScNbhdGerm E C} {G₂ : ScNbhdGerm F D} {f : E 0 → F 0} {g : F 0 → G 0}

lemma toBase_levelMap (hf : IsSc0Germ G₁ f) {m : ℕ} {x : E m} (hx : x ∈ G₁.U m) :
    F.toBase m (levelMap f m x) = f (E.toBase m x) :=
  Polyfold.toBase_levelMap (hf.mem_range m x hx)

lemma continuousOn_base (hf : IsSc0Germ G₁ f) : ContinuousOn f (G₁.U 0) := by
  have := hf.continuousOn 0
  simpa [funext (levelMap_zero f)] using this

/-- The level maps are compatible with the inclusions. -/
lemma incl_levelMap (hf : IsSc0Germ G₁ f) {m : ℕ} {x : E (m + 1)} (hx : x ∈ G₁.U (m + 1)) :
    F.incl m (levelMap f (m + 1) x) = levelMap f m (E.incl m x) := by
  apply F.toBase_injective m
  rw [← ScScale.toBase_succ, hf.toBase_levelMap hx, hf.toBase_levelMap (G₁.nested m x hx)]
  rfl

lemma inclK_levelMap (hf : IsSc0Germ G₁ f) {m k : ℕ} {x : E (m + k)} (hx : x ∈ G₁.U (m + k)) :
    F.inclK m k (levelMap f (m + k) x) = levelMap f m (E.inclK m k x) := by
  apply F.toBase_injective m
  rw [F.toBase_inclK, hf.toBase_levelMap hx, hf.toBase_levelMap (G₁.inclK_mem hx), E.toBase_inclK]

lemma mono (hf : IsSc0Germ G₁ f) {G₁' : ScNbhdGerm E C} (h : ∀ m, G₁'.U m ⊆ G₁.U m) :
    IsSc0Germ G₁' f :=
  ⟨fun m x hx => hf.mem_range m x (h m hx), fun m => (hf.continuousOn m).mono (h m)⟩

lemma levelMap_congr {f' : E 0 → F 0} (h : EqOn f f' (G₁.U 0)) {m : ℕ} {x : E m}
    (hx : x ∈ G₁.U m) : levelMap f m x = levelMap f' m x := by
  simp only [levelMap, h (G₁.toBase_mem hx)]

/-- sc⁰ depends only on the values on `U₀`. -/
lemma congr (hf : IsSc0Germ G₁ f) {f' : E 0 → F 0} (h : EqOn f f' (G₁.U 0)) : IsSc0Germ G₁ f' :=
  ⟨fun m x hx => by rw [← h (G₁.toBase_mem hx)]; exact hf.mem_range m x hx,
    fun m => (hf.continuousOn m).congr fun x hx => (levelMap_congr h hx).symm⟩

lemma levelMap_comp (hg : IsSc0Germ G₂ g) (hf : IsSc0Germ G₁ f) (hfV : G₁.MapsToGerm G₂ f) {m : ℕ}
    {x : E m} (hx : x ∈ G₁.U m) :
    levelMap (g ∘ f) m x = levelMap g m (levelMap f m x) := by
  apply levelMap_eq_of_toBase_eq
  rw [hg.toBase_levelMap (hfV m hx), hf.toBase_levelMap hx]
  rfl

/-- The composition of sc⁰-germs is an sc⁰-germ. -/
lemma comp (hg : IsSc0Germ G₂ g) (hf : IsSc0Germ G₁ f) (hfV : G₁.MapsToGerm G₂ f) :
    IsSc0Germ G₁ (g ∘ f) where
  mem_range m x hx := by
    change g (f (E.toBase m x)) ∈ _
    rw [← hf.toBase_levelMap hx]
    exact hg.mem_range m _ (hfV m hx)
  continuousOn m :=
    ((hg.continuousOn m).comp (hf.continuousOn m) (hfV m)).congr
      fun x hx => hg.levelMap_comp hf hfV hx

end IsSc0Germ

/-- An sc⁰ map on a relatively open `U ∋ 0` is an sc⁰-germ on `ofSet U`. -/
lemma IsSc0.isSc0Germ {U : Set (E 0)} (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C)
    (h0 : (0 : E 0) ∈ U) {f : E 0 → F 0} (hf : IsSc0 E F U f) :
    IsSc0Germ (ScNbhdGerm.ofSet hU h0) f :=
  ⟨hf.mem_range, hf.continuousOn⟩

/-- An sc-operator is an sc⁰-germ on every germ. -/
lemma ScOperator.isSc0Germ (T : ScOperator E F) (G₁ : ScNbhdGerm E C) : IsSc0Germ G₁ (T 0) :=
  ⟨fun m x _ => ⟨T m x, T.toBase_comm m x⟩, fun m => (T m).continuous.continuousOn.congr
    fun _ _ => levelMap_eq_of_toBase_eq (T.toBase_comm m _)⟩

/-! ### Definition 3.1.2 (preprint 3.2): sc¹-germs, sc^k-germs -/

/-- **Definition 3.1.2 (preprint 3.2)**: `f` is an **sc¹-germ with derivative family `D`** on `O(C, 0)`: an
sc⁰-germ, differentiable at every `x ∈ U₁` within `U₁` (in the sense of Definition 1.1.15 (preprint 1.14) (2)) with
derivative `D x ∘ ι₁`, whose tangent map is an sc⁰-germ on `TO(C, 0)`. -/
structure IsSc1GermWith (G : ScNbhdGerm E C) (f : E 0 → F 0) (D : E 1 → E 0 →L[ℝ] F 0) :
    Prop where
  isSc0 : IsSc0Germ G f
  hasFDerivWithinAt : ∀ x ∈ G.U 1,
    HasFDerivWithinAt (f ∘ E.toBase 1) ((D x).comp (E.toBase 1)) (G.U 1) x
  tangent_isSc0 : IsSc0Germ G.tangent (tangentMapWith f D)

/-- **Definition 3.1.2 (preprint 3.2)**: `f` is an **sc¹-germ** on `O(C, 0)`. -/
def IsSc1Germ (G : ScNbhdGerm E C) (f : E 0 → F 0) : Prop := ∃ D, IsSc1GermWith G f D

open scoped Classical in
/-- A choice of derivative family for the germ `f` on `G` (junk if `f` is not sc¹). -/
def scDerivGerm (G : ScNbhdGerm E C) (f : E 0 → F 0) : E 1 → E 0 →L[ℝ] F 0 :=
  if h : IsSc1Germ G f then h.choose else fun _ => 0

/-- The tangent germ `Tf` of `f` on `G`, with the chosen derivative. -/
def tangentMapGerm (G : ScNbhdGerm E C) (f : E 0 → F 0) : E.tangent 0 → F.tangent 0 :=
  tangentMapWith f (scDerivGerm G f)

namespace IsSc1GermWith

variable {G₁ : ScNbhdGerm E C} {f : E 0 → F 0} {D₁ : E 1 → E 0 →L[ℝ] F 0}

lemma isSc1Germ (h : IsSc1GermWith G₁ f D₁) : IsSc1Germ G₁ f := ⟨D₁, h⟩

/-- The first component of the level-`m` tangent map is the level-`(m+1)` map. -/
lemma levelMap_tangent_fst (h : IsSc1GermWith G₁ f D₁) {m : ℕ} {p : E.tangent m}
    (hp : p ∈ G₁.tangent.U m) :
    (levelMap (tangentMapWith f D₁) m p).1 = levelMap f (m + 1) p.1 := by
  have hp1 : p.1 ∈ G₁.U (m + 1) := hp.1
  have := congrArg Prod.fst (h.tangent_isSc0.toBase_levelMap hp)
  rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase] at this
  change F.shift.toBase m (levelMap (tangentMapWith f D₁) m p).1 =
    levelMap f 1 (E.shift.toBase m p.1) at this
  apply F.shift.toBase_injective m
  rw [this]
  apply F.toBase_injective 1
  rw [← F.shift_toBase, h.isSc0.toBase_levelMap hp1, h.isSc0.toBase_levelMap
    (G₁.shift_toBase_mem hp1), E.shift_toBase m p.1]

lemma tangentMapWith_mapsTo (h : IsSc1GermWith G₁ f D₁) {G₂ : ScNbhdGerm F D}
    (hfV : G₁.MapsToGerm G₂ f) : G₁.tangent.MapsToGerm G₂.tangent (tangentMapWith f D₁) := by
  intro m p hp
  rw [ScNbhdGerm.mem_tangent_U, h.levelMap_tangent_fst hp]
  exact hfV (m + 1) hp.1

/-- `(x, h) ↦ Df(x)h` is continuous on `U₁ × E₀`. -/
lemma continuousOn_deriv (h : IsSc1GermWith G₁ f D₁) :
    ContinuousOn (fun p : E 1 × E 0 => D₁ p.1 p.2) (G₁.U 1 ×ˢ univ) := by
  have := h.tangent_isSc0.continuousOn 0
  refine (continuous_snd.comp_continuousOn this).congr fun p _ => ?_
  change D₁ p.1 p.2 = (levelMap (tangentMapWith f D₁) 0 p).2
  rw [levelMap_zero]; rfl

lemma congr (h : IsSc1GermWith G₁ f D₁) {f' : E 0 → F 0} (hff' : EqOn f f' (G₁.U 0)) :
    IsSc1GermWith G₁ f' D₁ where
  isSc0 := h.isSc0.congr hff'
  hasFDerivWithinAt x hx :=
    (h.hasFDerivWithinAt x hx).congr' (fun y hy => (hff' (G₁.toBase_mem hy)).symm) hx
  tangent_isSc0 := h.tangent_isSc0.congr fun p hp => by
    change (levelMap f 1 p.1, D₁ p.1 p.2) = (levelMap f' 1 p.1, D₁ p.1 p.2)
    rw [IsSc0Germ.levelMap_congr hff' (G₁.mem_tangent_U.1 hp)]

lemma mono (h : IsSc1GermWith G₁ f D₁) {G₁' : ScNbhdGerm E C} (hsub : ∀ m, G₁'.U m ⊆ G₁.U m) :
    IsSc1GermWith G₁' f D₁ where
  isSc0 := h.isSc0.mono hsub
  hasFDerivWithinAt x hx := (h.hasFDerivWithinAt x (hsub 1 hx)).mono (hsub 1)
  tangent_isSc0 := h.tangent_isSc0.mono fun m _ hp =>
    (ScNbhdGerm.mem_tangent_U _).2 (hsub (m + 1) ((ScNbhdGerm.mem_tangent_U _).1 hp))

/-- The derivative family is unique on `U₁`. -/
lemma eq_of_uniqueDiffWithinAt (h : IsSc1GermWith G₁ f D₁) {D' : E 1 → E 0 →L[ℝ] F 0}
    (h' : IsSc1GermWith G₁ f D') {x : E 1} (hx : x ∈ G₁.U 1)
    (hU : UniqueDiffWithinAt ℝ (G₁.U 1) x) : D₁ x = D' x := by
  have h1 := hU.eq (h.hasFDerivWithinAt x hx) (h'.hasFDerivWithinAt x hx)
  have hd : Dense (Submodule.span ℝ (range (E.toBase 1)) : Set (E 0)) :=
    Dense.mono Submodule.subset_span (E.denseRange_inclK 0 1)
  refine ContinuousLinearMap.ext_on hd ?_
  rintro _ ⟨y, rfl⟩
  exact congrArg (fun L : E 1 →L[ℝ] F 0 => L y) h1

end IsSc1GermWith

namespace IsSc1Germ

variable {G₁ : ScNbhdGerm E C} {f : E 0 → F 0}

lemma isSc1GermWith_scDerivGerm (h : IsSc1Germ G₁ f) : IsSc1GermWith G₁ f (scDerivGerm G₁ f) := by
  rw [scDerivGerm, dif_pos h]; exact h.choose_spec

lemma isSc0 (h : IsSc1Germ G₁ f) : IsSc0Germ G₁ f := h.isSc1GermWith_scDerivGerm.isSc0

lemma tangentMapGerm_isSc0 (h : IsSc1Germ G₁ f) :
    IsSc0Germ G₁.tangent (tangentMapGerm G₁ f) :=
  h.isSc1GermWith_scDerivGerm.tangent_isSc0

lemma scDerivGerm_eqOn (hC : IsQuadrantLike E C) {D₁ : E 1 → E 0 →L[ℝ] F 0}
    (h : IsSc1GermWith G₁ f D₁) : EqOn (scDerivGerm G₁ f) D₁ (G₁.U 1) :=
  fun x hx => h.isSc1Germ.isSc1GermWith_scDerivGerm.eq_of_uniqueDiffWithinAt h hx
    (G₁.uniqueDiffWithinAt hC 1 hx)

lemma tangentMapGerm_eqOn (hC : IsQuadrantLike E C) {D₁ : E 1 → E 0 →L[ℝ] F 0}
    (h : IsSc1GermWith G₁ f D₁) :
    EqOn (tangentMapGerm G₁ f) (tangentMapWith f D₁) (G₁.tangent.U 0) := by
  intro p hp
  change (levelMap f 1 p.1, scDerivGerm G₁ f p.1 p.2) = (levelMap f 1 p.1, D₁ p.1 p.2)
  rw [scDerivGerm_eqOn hC h hp.1]

lemma congr (h : IsSc1Germ G₁ f) {f' : E 0 → F 0} (hff' : EqOn f f' (G₁.U 0)) : IsSc1Germ G₁ f' :=
  ⟨_, h.isSc1GermWith_scDerivGerm.congr hff'⟩

lemma mono (h : IsSc1Germ G₁ f) {G₁' : ScNbhdGerm E C} (hsub : ∀ m, G₁'.U m ⊆ G₁.U m) :
    IsSc1Germ G₁' f := ⟨_, h.isSc1GermWith_scDerivGerm.mono hsub⟩

lemma tangentMapGerm_congr (hC : IsQuadrantLike E C) (h : IsSc1Germ G₁ f) {f' : E 0 → F 0}
    (hff' : EqOn f f' (G₁.U 0)) :
    EqOn (tangentMapGerm G₁ f) (tangentMapGerm G₁ f') (G₁.tangent.U 0) := by
  have h1 : IsSc1GermWith G₁ f' (scDerivGerm G₁ f) := h.isSc1GermWith_scDerivGerm.congr hff'
  refine EqOn.trans ?_ (tangentMapGerm_eqOn hC h1).symm
  intro p hp
  change (levelMap f 1 p.1, scDerivGerm G₁ f p.1 p.2) = (levelMap f' 1 p.1, scDerivGerm G₁ f p.1 p.2)
  rw [IsSc0Germ.levelMap_congr hff' (G₁.mem_tangent_U.1 hp)]

/-- The tangent germs built on `G'` and on a larger `G` agree on `TG'`. -/
lemma tangentMapGerm_mono (hC : IsQuadrantLike E C) (h : IsSc1Germ G₁ f) {G₁' : ScNbhdGerm E C}
    (hsub : ∀ m, G₁'.U m ⊆ G₁.U m) :
    EqOn (tangentMapGerm G₁' f) (tangentMapGerm G₁ f) (G₁'.tangent.U 0) :=
  tangentMapGerm_eqOn hC (h.isSc1GermWith_scDerivGerm.mono hsub)

end IsSc1Germ

/-- **Definition 3.1.2 (preprint 3.2)**: `f` is an **sc^k-germ** on `O(C, 0)`: sc⁰ for `k = 0`; for `k + 1`, sc¹
with `Tf` an sc^k-germ on `TO(C, 0)`. -/
def IsSckGerm : ℕ → ∀ {E F : ScBanach} {C : Set (E 0)}, ScNbhdGerm E C → (E 0 → F 0) → Prop
  | 0, _, _, _, G, f => IsSc0Germ G f
  | k + 1, _, _, _, G, f => IsSc1Germ G f ∧ IsSckGerm k G.tangent (tangentMapGerm G f)

/-- **Definition 3.1.2 (preprint 3.2)**: `f` is an **sc-smooth germ** on `O(C, 0)`. -/
def IsScSmoothGerm (G : ScNbhdGerm E C) (f : E 0 → F 0) : Prop := ∀ k, IsSckGerm k G f

lemma isSckGerm_zero_iff {G₁ : ScNbhdGerm E C} {f : E 0 → F 0} :
    IsSckGerm 0 G₁ f ↔ IsSc0Germ G₁ f := Iff.rfl

lemma isSckGerm_succ_iff {k : ℕ} {G₁ : ScNbhdGerm E C} {f : E 0 → F 0} :
    IsSckGerm (k + 1) G₁ f ↔ IsSc1Germ G₁ f ∧ IsSckGerm k G₁.tangent (tangentMapGerm G₁ f) :=
  Iff.rfl

lemma IsSckGerm.isSc0 : ∀ {k : ℕ} {E F : ScBanach} {C : Set (E 0)} {G₁ : ScNbhdGerm E C}
    {f : E 0 → F 0}, IsSckGerm k G₁ f → IsSc0Germ G₁ f
  | 0, _, _, _, _, _, h => h
  | _ + 1, _, _, _, _, _, h => h.1.isSc0

lemma IsSckGerm.isSc1 {k : ℕ} {G₁ : ScNbhdGerm E C} {f : E 0 → F 0} (h : IsSckGerm (k + 1) G₁ f) :
    IsSc1Germ G₁ f := h.1

lemma IsSckGerm.of_succ : ∀ {k : ℕ} {E F : ScBanach} {C : Set (E 0)} {G₁ : ScNbhdGerm E C}
    {f : E 0 → F 0}, IsSckGerm (k + 1) G₁ f → IsSckGerm k G₁ f
  | 0, _, _, _, _, _, h => h.1.isSc0
  | k + 1, _, _, _, _, _, h => ⟨h.1, IsSckGerm.of_succ (k := k) h.2⟩

lemma IsSckGerm.of_le {k l : ℕ} (hkl : k ≤ l) {G₁ : ScNbhdGerm E C} {f : E 0 → F 0}
    (h : IsSckGerm l G₁ f) : IsSckGerm k G₁ f := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact ih h.of_succ

lemma IsScSmoothGerm.isSckGerm {G₁ : ScNbhdGerm E C} {f : E 0 → F 0} (h : IsScSmoothGerm G₁ f)
    (k : ℕ) : IsSckGerm k G₁ f := h k

lemma isScSmoothGerm_iff {G₁ : ScNbhdGerm E C} {f : E 0 → F 0} :
    IsScSmoothGerm G₁ f ↔ IsSc1Germ G₁ f ∧ IsScSmoothGerm G₁.tangent (tangentMapGerm G₁ f) :=
  ⟨fun h => ⟨(h 1).isSc1, fun k => (h (k + 1)).2⟩, fun h k => by
    cases k with
    | zero => exact h.1.isSc0
    | succ k => exact ⟨h.1, h.2 k⟩⟩

/-- sc^k-germs depend only on the values on `U₀`. -/
theorem IsSckGerm.congr : ∀ {k : ℕ} {E F : ScBanach} {C : Set (E 0)} {G₁ : ScNbhdGerm E C}
    {f f' : E 0 → F 0}, IsQuadrantLike E C → EqOn f f' (G₁.U 0) → IsSckGerm k G₁ f →
    IsSckGerm k G₁ f'
  | 0, _, _, _, _, _, _, _, hff', h => IsSc0Germ.congr h hff'
  | k + 1, _, _, _, _, _, _, hC, hff', h =>
    ⟨h.1.congr hff', IsSckGerm.congr (k := k) hC.tangentSet (h.1.tangentMapGerm_congr hC hff') h.2⟩

/-- sc^k-germs restrict to smaller germs. -/
theorem IsSckGerm.mono : ∀ {k : ℕ} {E F : ScBanach} {C : Set (E 0)} {G₁ G₁' : ScNbhdGerm E C}
    {f : E 0 → F 0}, IsQuadrantLike E C → (∀ m, G₁'.U m ⊆ G₁.U m) → IsSckGerm k G₁ f →
    IsSckGerm k G₁' f
  | 0, _, _, _, _, _, _, _, hsub, h => IsSc0Germ.mono h hsub
  | k + 1, _, _, _, _, _, _, hC, hsub, h => by
    refine ⟨h.1.mono hsub, ?_⟩
    have := IsSckGerm.mono (k := k) hC.tangentSet
      (fun m _ hp => (ScNbhdGerm.mem_tangent_U _).2 (hsub (m + 1) ((ScNbhdGerm.mem_tangent_U _).1 hp)))
      h.2
    exact IsSckGerm.congr hC.tangentSet (h.1.tangentMapGerm_mono hC hsub).symm this

theorem IsScSmoothGerm.mono {G₁ G₁' : ScNbhdGerm E C} {f : E 0 → F 0} (hC : IsQuadrantLike E C)
    (hsub : ∀ m, G₁'.U m ⊆ G₁.U m) (h : IsScSmoothGerm G₁ f) : IsScSmoothGerm G₁' f :=
  fun k => (h k).mono hC hsub

/-! ### The bridge from Chapter 1: sc^k maps are sc^k-germs -/

/-- The chosen derivative of `f` on `U` and on the germ `ofSet U` agree on `U₁`. -/
lemma IsSc1.scDerivGerm_ofSet_eqOn {U : Set (E 0)} (hC : IsQuadrantLike E C)
    (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C) (h0 : (0 : E 0) ∈ U) {f : E 0 → F 0}
    (hf : IsSc1 U f) :
    EqOn (tangentMapGerm (ScNbhdGerm.ofSet hU h0) f) (tangentMap U f)
      ((ScNbhdGerm.ofSet hU h0).tangent.U 0) := by
  have h1 : IsSc1GermWith (ScNbhdGerm.ofSet hU h0) f (scDeriv U f) :=
    ⟨hf.isSc0.isSc0Germ hU h0, hf.isSc1With_scDeriv.hasFDerivWithinAt,
      by
        have := hf.tangentMap_isSc0
        rw [ScNbhdGerm.ofSet_tangent]
        exact this.isSc0Germ _ _⟩
  exact IsSc1Germ.tangentMapGerm_eqOn hC h1

/-- **The special example of Definition 3.1.1 (preprint 3.1)**: an sc^k map on a relatively open `U ∋ 0` in `C`
is an sc^k-germ on `ofSet U`. -/
theorem IsSck.isSckGerm : ∀ {k : ℕ} {E F : ScBanach} {C U : Set (E 0)}, IsQuadrantLike E C →
    ∀ (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C) (h0 : (0 : E 0) ∈ U) {f : E 0 → F 0},
    IsSck k E F U f → IsSckGerm k (ScNbhdGerm.ofSet hU h0) f
  | 0, _, _, _, _, _, hU, h0, _, h => IsSc0.isSc0Germ hU h0 h
  | k + 1, E, F, C, U, hC, hU, h0, f, h => by
    refine ⟨⟨scDeriv U f, h.1.isSc0.isSc0Germ hU h0, h.1.isSc1With_scDeriv.hasFDerivWithinAt, ?_⟩,
      ?_⟩
    · rw [ScNbhdGerm.ofSet_tangent]; exact h.1.tangentMap_isSc0.isSc0Germ _ _
    · have := IsSck.isSckGerm (k := k) hC.tangentSet (ScNbhdGerm.tangentSet_relOpen hU)
        (ScNbhdGerm.zero_mem_tangentSet h0) h.2
      rw [← ScNbhdGerm.ofSet_tangent hU h0] at this
      exact IsSckGerm.congr hC.tangentSet (h.1.scDerivGerm_ofSet_eqOn hC hU h0).symm this

theorem IsScSmooth.isScSmoothGerm {U : Set (E 0)} (hC : IsQuadrantLike E C)
    (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C) (h0 : (0 : E 0) ∈ U) {f : E 0 → F 0}
    (hf : IsScSmooth U f) : IsScSmoothGerm (ScNbhdGerm.ofSet hU h0) f :=
  fun k => (hf k).isSckGerm hC hU h0


/-! ### The chain rule for germs (Theorem 1.3.1 (preprint 1.21) for germs; the proof of §1.4.2) -/

namespace IsSc1GermWith

variable {G₁ : ScNbhdGerm E C} {G₂ : ScNbhdGerm F D} {f : E 0 → F 0} {g : F 0 → G 0}
  {Df : E 1 → E 0 →L[ℝ] F 0} {Dg : F 1 → F 0 →L[ℝ] G 0}

/-- The mean value inequality along a segment in `V₁`. -/
private lemma norm_sub_le_of_segment (hg : IsSc1GermWith G₂ g Dg) {y₀ k : F 1}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, y₀ + t • k ∈ G₂.U 1) {K : ℝ}
    (hK : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Dg (y₀ + t • k) (F.toBase 1 k) - Dg y₀ (F.toBase 1 k)‖ ≤ K) :
    ‖g (F.toBase 1 (y₀ + k)) - g (F.toBase 1 y₀) - Dg y₀ (F.toBase 1 k)‖ ≤ K := by
  set φ : ℝ → G 0 := fun t => g (F.toBase 1 (y₀ + t • k)) - t • Dg y₀ (F.toBase 1 k) with hφ
  have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => y₀ + t • k) k t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const k).const_add y₀
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ
      (Dg (y₀ + t • k) (F.toBase 1 k) - Dg y₀ (F.toBase 1 k)) (Icc 0 1) t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun t : ℝ => g (F.toBase 1 (y₀ + t • k)))
        (((Dg (y₀ + t • k)).comp (F.toBase 1)) k) (Icc 0 1) t :=
      HasFDerivWithinAt.comp_hasDerivWithinAt (l := g ∘ F.toBase 1) (f := fun t : ℝ => y₀ + t • k)
        t (hg.hasFDerivWithinAt _ (hseg t ht)) (hγ t).hasDerivWithinAt hseg
    have h2 : HasDerivWithinAt (fun t : ℝ => t • Dg y₀ (F.toBase 1 k)) (Dg y₀ (F.toBase 1 k))
        (Icc 0 1) t := by
      simpa using ((hasDerivAt_id t).smul_const (Dg y₀ (F.toBase 1 k))).hasDerivWithinAt
    exact h1.sub h2
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hK (convex_Icc 0 1)
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  have h01 : φ 1 - φ 0 = g (F.toBase 1 (y₀ + k)) - g (F.toBase 1 y₀) - Dg y₀ (F.toBase 1 k) := by
    simp only [hφ, one_smul, zero_smul, add_zero, sub_zero]; abel
  rwa [h01, sub_zero, norm_one, mul_one] at this

/-- Uniform smallness of `[Dg(y) − Dg(y₀)](w + b)` for `y` near `y₀` in `V₁`, `w` in a compact set
and `b` small. -/
private lemma exists_delta (hg : IsSc1GermWith G₂ g Dg) {y₀ : F 1} (hy₀ : y₀ ∈ G₂.U 1)
    {K : Set (F 0)} (hK : IsCompact K) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ y ∈ G₂.U 1, ‖y - y₀‖ < δ → ∀ w ∈ K, ∀ b : F 0, ‖b‖ < δ →
      ‖Dg y (w + b) - Dg y₀ (w + b)‖ ≤ c := by
  let Θ : (G₂.U 1 × F 0) × F 0 → G 0 :=
    fun q => Dg q.1.1.1 (q.2 + q.1.2) - Dg y₀ (q.2 + q.1.2)
  have hΘ : Continuous Θ := by
    have h1 : Continuous fun q : (G₂.U 1 × F 0) × F 0 => Dg q.1.1.1 (q.2 + q.1.2) := by
      refine hg.continuousOn_deriv.comp_continuous
        (f := fun q : (G₂.U 1 × F 0) × F 0 => ((q.1.1.1 : F 1), q.2 + q.1.2)) ?_ ?_
      · fun_prop
      · intro q; exact ⟨q.1.1.2, mem_univ _⟩
    exact h1.sub ((Dg y₀).continuous.comp (by fun_prop))
  have key : ∀ᶠ q in 𝓝 ((⟨y₀, hy₀⟩, (0 : F 0)) : G₂.U 1 × F 0), ∀ w ∈ K,
      ‖Θ (q, w)‖ ≤ c := by
    refine hK.eventually_forall_of_forall_eventually (P := fun q w => ‖Θ (q, w)‖ ≤ c) fun w _ => ?_
    have h0 : Θ ((⟨y₀, hy₀⟩, 0), w) = 0 := by simp [Θ]
    have := hΘ.continuousAt.eventually_mem (x := ((⟨y₀, hy₀⟩, 0), w))
      (s := Metric.closedBall 0 c) (by rw [h0]; exact Metric.closedBall_mem_nhds 0 hc)
    exact this.mono fun q hq => by simpa using hq
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 key
  refine ⟨δ, hδ, fun y hy hyδ w hw b hb => ?_⟩
  have := hδ' (y := (⟨y, hy⟩, b)) ?_ w hw
  · simpa [Θ] using this
  · rw [Prod.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_zero_right]
    exact max_lt hyδ hb

/-- The derivative part of the chain rule for germs: `g ∘ f : U₁ → G₀` is differentiable at
`x ∈ U₁` within `U₁` with derivative `Dg(f(x)) ∘ Df(x)`. -/
theorem hasFDerivWithinAt_comp
    (hV : ∃ O K : Set (F 1), IsOpen O ∧ Convex ℝ K ∧ G₂.U 1 = O ∩ K)
    (hg : IsSc1GermWith G₂ g Dg) (hf : IsSc1GermWith G₁ f Df) (hfV : G₁.MapsToGerm G₂ f) {x : E 1}
    (hx : x ∈ G₁.U 1) :
    HasFDerivWithinAt (g ∘ f ∘ E.toBase 1)
      (((Dg (levelMap f 1 x)).comp (Df x)).comp (E.toBase 1)) (G₁.U 1) x := by
  obtain ⟨O, K', hO, hK', hVOC⟩ := hV
  set ι := E.toBase 1 with hι
  set ιF := F.toBase 1 with hιF
  set f₁ := levelMap f 1 with hf₁
  set y₀ := f₁ x with hy₀
  have hy₀V : y₀ ∈ G₂.U 1 := hfV 1 hx
  have hιF_f₁ : ∀ z ∈ G₁.U 1, ιF (f₁ z) = f (ι z) := fun z hz => hf.isSc0.toBase_levelMap hz
  obtain ⟨K₀, hK₀, hK₀sub⟩ :=
    (E.incl_isCompactOperator 0).image_closedBall_subset_compact (f := (E.incl 0 : E 1 →ₗ[ℝ] E 0)) 1
  set K := Df x '' K₀ with hK
  have hKc : IsCompact K := hK₀.image (Df x).continuous
  have hy₀O : y₀ ∈ O := (hVOC ▸ hy₀V).1
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO y₀ hy₀O
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have hc2 : 0 < c / 2 := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := hg.exists_delta hy₀V hKc hc2
  set ε := min (δ / 2) (c / 2 / (‖Dg y₀‖ + 1)) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hεc : ‖Dg y₀‖ * ε ≤ c / 2 := by
    calc ‖Dg y₀‖ * ε ≤ (‖Dg y₀‖ + 1) * (c / 2 / (‖Dg y₀‖ + 1)) :=
          mul_le_mul (by linarith) (min_le_right _ _) hε0.le (by positivity)
      _ = c / 2 := by field_simp
  have ev1 : ∀ᶠ z in 𝓝[G₁.U 1] x, z ∈ G₁.U 1 := self_mem_nhdsWithin
  have ev2 : ∀ᶠ z in 𝓝[G₁.U 1] x, dist (f₁ z) (f₁ x) < min ρ δ :=
    Metric.tendsto_nhds.1 (hf.isSc0.continuousOn 1 x hx) _ (lt_min hρ hδ)
  have ev3 : ∀ᶠ z in 𝓝[G₁.U 1] x,
      ‖(f ∘ ι) z - (f ∘ ι) x - ((Df x).comp ι) (z - x)‖ ≤ ε * ‖z - x‖ :=
    isLittleO_iff.1 (hasFDerivWithinAt_iff_isLittleO.1 (hf.hasFDerivWithinAt x hx)) hε0
  filter_upwards [ev1, ev2, ev3] with z hz hz2 hz3
  set r := f (ι z) - f (ι x) - Df x (ι (z - x)) with hr
  have hr' : ‖r‖ ≤ ε * ‖z - x‖ := hz3
  have hsplit : f (ι z) - f (ι x) = Df x (ι (z - x)) + r := by rw [hr]; abel
  set k := f₁ z - y₀ with hk
  have hιk : ιF k = f (ι z) - f (ι x) := by
    rw [hk, map_sub, hιF_f₁ z hz, hy₀, hιF_f₁ x hx]
  have hknorm : ‖k‖ < min ρ δ := by rwa [hk, ← dist_eq_norm]
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, y₀ + t • k ∈ G₂.U 1 := by
    intro t ht
    rw [hVOC]
    refine ⟨hρO ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      calc t * ‖k‖ ≤ 1 * ‖k‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ < ρ := by rw [one_mul]; exact lt_of_lt_of_le hknorm (min_le_left _ _)
    · have h1 : y₀ ∈ K' := (hVOC ▸ hy₀V).2
      have h2 : f₁ z ∈ K' := (hVOC ▸ hfV 1 hz).2
      have := hK'.add_smul_sub_mem h1 h2 ht
      rwa [hk]
  have hmain : ‖g (f (ι z)) - g (f (ι x)) - Dg y₀ (ιF k)‖ ≤ c / 2 * ‖z - x‖ := by
    by_cases hzx : z = x
    · subst hzx
      simp [hk, hy₀]
    have hs : 0 < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hzx)
    set s := ‖z - x‖ with hs_def
    set u : E 1 := s⁻¹ • (z - x) with hu
    have hu1 : u ∈ Metric.closedBall (0 : E 1) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, hu, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hs.ne']
    set w₁ := Df x (ι u) with hw₁
    have hw₁K : w₁ ∈ K := ⟨ι u, hK₀sub ⟨u, hu1, rfl⟩, rfl⟩
    set b := s⁻¹ • r with hb
    have hbδ : ‖b‖ < δ := by
      rw [hb, norm_smul, norm_inv, norm_norm]
      calc s⁻¹ * ‖r‖ ≤ s⁻¹ * (ε * s) := by gcongr
        _ = ε := by field_simp
        _ ≤ δ / 2 := hεδ
        _ < δ := by linarith
    have hιk' : ιF k = s • (w₁ + b) := by
      rw [hιk, hsplit, hw₁, hb, smul_add, ← map_smul, ← map_smul, hu, smul_inv_smul₀ hs.ne',
        smul_inv_smul₀ hs.ne']
    have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖Dg (y₀ + t • k) (ιF k) - Dg y₀ (ιF k)‖ ≤ c / 2 * s := by
      intro t ht
      have hyδ : ‖y₀ + t • k - y₀‖ < δ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        calc t * ‖k‖ ≤ 1 * ‖k‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
          _ < δ := by rw [one_mul]; exact lt_of_lt_of_le hknorm (min_le_right _ _)
      have := hδ' _ (hseg t ht) hyδ w₁ hw₁K b hbδ
      rw [hιk', map_smul, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
        mul_comm]
      exact mul_le_mul_of_nonneg_right this hs.le
    have := hg.norm_sub_le_of_segment hseg hbound
    rwa [hk, add_sub_cancel, hιF_f₁ z hz, hy₀, hιF_f₁ x hx] at this
  have hsecond : ‖Dg y₀ r‖ ≤ c / 2 * ‖z - x‖ :=
    calc ‖Dg y₀ r‖ ≤ ‖Dg y₀‖ * ‖r‖ := (Dg y₀).le_opNorm r
      _ ≤ ‖Dg y₀‖ * (ε * ‖z - x‖) := by gcongr
      _ = ‖Dg y₀‖ * ε * ‖z - x‖ := by ring
      _ ≤ c / 2 * ‖z - x‖ := by gcongr
  have hid : (g ∘ f ∘ ι) z - (g ∘ f ∘ ι) x - (((Dg y₀).comp (Df x)).comp ι) (z - x)
      = (g (f (ι z)) - g (f (ι x)) - Dg y₀ (ιF k)) + Dg y₀ r := by
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hιk, hsplit, map_add]
    abel
  rw [hid]
  calc ‖(g (f (ι z)) - g (f (ι x)) - Dg y₀ (ιF k)) + Dg y₀ r‖
      ≤ ‖g (f (ι z)) - g (f (ι x)) - Dg y₀ (ιF k)‖ + ‖Dg y₀ r‖ := norm_add_le _ _
    _ ≤ c / 2 * ‖z - x‖ + c / 2 * ‖z - x‖ := add_le_add hmain hsecond
    _ = c * ‖z - x‖ := by ring

lemma tangentMapWith_comp (hg : IsSc0Germ G₂ g) (hf : IsSc0Germ G₁ f) (hfV : G₁.MapsToGerm G₂ f) :
    EqOn (tangentMapWith (g ∘ f) fun x => (Dg (levelMap f 1 x)).comp (Df x))
      (tangentMapWith g Dg ∘ tangentMapWith f Df) (G₁.tangent.U 0) := by
  intro p hp
  change (levelMap (g ∘ f) 1 p.1, Dg (levelMap f 1 p.1) (Df p.1 p.2)) =
    (levelMap g 1 (levelMap f 1 p.1), Dg (levelMap f 1 p.1) (Df p.1 p.2))
  rw [hg.levelMap_comp hf hfV (G₁.mem_tangent_U.1 hp)]

/-- **The chain rule for sc¹-germs with given derivatives.** -/
theorem comp (hV : ∃ O K : Set (F 1), IsOpen O ∧ Convex ℝ K ∧ G₂.U 1 = O ∩ K)
    (hg : IsSc1GermWith G₂ g Dg) (hf : IsSc1GermWith G₁ f Df) (hfV : G₁.MapsToGerm G₂ f) :
    IsSc1GermWith G₁ (g ∘ f) fun x => (Dg (levelMap f 1 x)).comp (Df x) where
  isSc0 := hg.isSc0.comp hf.isSc0 hfV
  hasFDerivWithinAt _ hx := hg.hasFDerivWithinAt_comp hV hf hfV hx
  tangent_isSc0 :=
    (hg.tangent_isSc0.comp hf.tangent_isSc0 (hf.tangentMapWith_mapsTo hfV)).congr
      (tangentMapWith_comp hg.isSc0 hf.isSc0 hfV).symm

end IsSc1GermWith

/-- The chain rule for sc¹-germs: `g ∘ f` is sc¹ and `T(g ∘ f) = Tg ∘ Tf` on `TU`. -/
theorem IsSc1Germ.comp {G₁ : ScNbhdGerm E C} {G₂ : ScNbhdGerm F D} {f : E 0 → F 0} {g : F 0 → G 0}
    (hC : IsQuadrantLike E C) (hD : IsQuadrantLike F D) (hg : IsSc1Germ G₂ g) (hf : IsSc1Germ G₁ f)
    (hfV : G₁.MapsToGerm G₂ f) :
    IsSc1Germ G₁ (g ∘ f) ∧ EqOn (tangentMapGerm G₁ (g ∘ f))
      (tangentMapGerm G₂ g ∘ tangentMapGerm G₁ f) (G₁.tangent.U 0) := by
  have hcomp := hg.isSc1GermWith_scDerivGerm.comp (G₂.relOpenConvex hD 1)
    hf.isSc1GermWith_scDerivGerm hfV
  refine ⟨hcomp.isSc1Germ, ?_⟩
  exact (IsSc1Germ.tangentMapGerm_eqOn hC hcomp).trans
    (IsSc1GermWith.tangentMapWith_comp hg.isSc0 hf.isSc0 hfV)

/-- **The chain rule for sc^k-germs** (Theorem 1.3.1 (preprint 1.21), iterated, for germs). -/
theorem IsSckGerm.comp : ∀ {k : ℕ} {E F G : ScBanach} {C : Set (E 0)} {D : Set (F 0)}
    {G₁ : ScNbhdGerm E C} {G₂ : ScNbhdGerm F D} {f : E 0 → F 0} {g : F 0 → G 0},
    IsQuadrantLike E C → IsQuadrantLike F D → IsSckGerm k G₂ g → IsSckGerm k G₁ f →
    G₁.MapsToGerm G₂ f → IsSckGerm k G₁ (g ∘ f)
  | 0, _, _, _, _, _, _, _, _, _, _, _, hg, hf, hfV => IsSc0Germ.comp hg hf hfV
  | k + 1, _, _, _, _, _, _, _, _, _, hC, hD, hg, hf, hfV => by
    obtain ⟨h1, h2⟩ := IsSc1Germ.comp hC hD hg.1 hf.1 hfV
    refine ⟨h1, ?_⟩
    have := IsSckGerm.comp (k := k) hC.tangentSet hD.tangentSet hg.2 hf.2
      (hf.1.isSc1GermWith_scDerivGerm.tangentMapWith_mapsTo hfV)
    exact IsSckGerm.congr hC.tangentSet h2.symm this

theorem IsScSmoothGerm.comp {G₁ : ScNbhdGerm E C} {G₂ : ScNbhdGerm F D} {f : E 0 → F 0}
    {g : F 0 → G 0} (hC : IsQuadrantLike E C) (hD : IsQuadrantLike F D) (hg : IsScSmoothGerm G₂ g)
    (hf : IsScSmoothGerm G₁ f) (hfV : G₁.MapsToGerm G₂ f) : IsScSmoothGerm G₁ (g ∘ f) :=
  fun k => IsSckGerm.comp hC hD (hg k) (hf k) hfV

/-! ### Sc-operators are sc-smooth germs -/

namespace ScOperator

variable (T : ScOperator E F)

/-- The tangent `TT = (T, T) : TE → TF` of an sc-operator, again an sc-operator. -/
def tangentOp : ScOperator E.tangent F.tangent where
  lvl m := (T (m + 1)).prodMap (T m)
  incl_comm m p := by
    change (F.incl (m + 1) (T (m + 2) p.1), F.incl m (T (m + 1) p.2)) =
      (T (m + 1) (E.incl (m + 1) p.1), T m (E.incl m p.2))
    rw [T.incl_comm, T.incl_comm]

lemma tangentMapWith_eq : tangentMapWith (T 0) (fun _ => T 0) = T.tangentOp 0 := by
  funext p
  change (levelMap (T 0) 1 p.1, T 0 p.2) = (T 1 p.1, T 0 p.2)
  rw [T.levelMap_eq]

lemma isSc1GermWith (G₁ : ScNbhdGerm E C) : IsSc1GermWith G₁ (T 0) fun _ => T 0 where
  isSc0 := T.isSc0Germ G₁
  hasFDerivWithinAt _ _ := ((T 0).comp (E.toBase 1)).hasFDerivWithinAt
  tangent_isSc0 := by rw [T.tangentMapWith_eq]; exact T.tangentOp.isSc0Germ _

/-- An sc-operator is an sc^k-germ on every germ, for every `k`. -/
theorem isSckGerm : ∀ (k : ℕ) {E F : ScBanach} (T : ScOperator E F) {C : Set (E 0)}
    (G₁ : ScNbhdGerm E C), IsQuadrantLike E C → IsSckGerm k G₁ (T 0)
  | 0, _, _, T, _, G₁, _ => T.isSc0Germ G₁
  | k + 1, _, _, T, _, G₁, hC => by
    refine ⟨(T.isSc1GermWith G₁).isSc1Germ, ?_⟩
    have h1 : EqOn (tangentMapGerm G₁ (T 0)) (T.tangentOp 0) (G₁.tangent.U 0) := by
      rw [← T.tangentMapWith_eq]
      exact IsSc1Germ.tangentMapGerm_eqOn hC (T.isSc1GermWith G₁)
    exact IsSckGerm.congr hC.tangentSet h1.symm (isSckGerm k T.tangentOp G₁.tangent hC.tangentSet)

theorem isScSmoothGerm (G₁ : ScNbhdGerm E C) (hC : IsQuadrantLike E C) :
    IsScSmoothGerm G₁ (T 0) := fun k => T.isSckGerm k G₁ hC

end ScOperator

/-- Composition with an sc-operator on the outside preserves sc^k-germs. -/
theorem IsSckGerm.operator_comp {k : ℕ} {G₁ : ScNbhdGerm E C} {f : E 0 → F 0} (hC : IsQuadrantLike E C)
    (T : ScOperator F G) (hf : IsSckGerm k G₁ f) : IsSckGerm k G₁ (T 0 ∘ f) :=
  IsSckGerm.comp hC (isQuadrantLike_univ F) (T.isSckGerm k (ScNbhdGerm.full F) (isQuadrantLike_univ F))
    hf (G₁.mapsToGerm_full f)

/-! ### Pairings -/

/-- The pairing `(f, g) : E → F ⊕ G`. -/
def pairMap (f : E 0 → F 0) (g : E 0 → G 0) : E 0 → (F.prod G) 0 := fun x => (f x, g x)

lemma IsSc0Germ.levelMap_pair {G₁ : ScNbhdGerm E C} {f : E 0 → F 0} {g : E 0 → G 0}
    (hf : IsSc0Germ G₁ f) (hg : IsSc0Germ G₁ g) {m : ℕ} {x : E m} (hx : x ∈ G₁.U m) :
    levelMap (pairMap f g) m x = ((levelMap f m x, levelMap g m x) : (F.prod G) m) := by
  apply levelMap_eq_of_toBase_eq
  rw [ScBanach.prod_toBase, hf.toBase_levelMap hx, hg.toBase_levelMap hx]
  rfl

lemma IsSc0Germ.pair {G₁ : ScNbhdGerm E C} {f : E 0 → F 0} {g : E 0 → G 0}
    (hf : IsSc0Germ G₁ f) (hg : IsSc0Germ G₁ g) : IsSc0Germ G₁ (pairMap f g) where
  mem_range m x hx := ⟨(levelMap f m x, levelMap g m x), by
    rw [ScBanach.prod_toBase, hf.toBase_levelMap hx, hg.toBase_levelMap hx]; rfl⟩
  continuousOn m := ((hf.continuousOn m).prodMk (hg.continuousOn m)).congr
    fun x hx => hf.levelMap_pair hg hx

/-- The sc-isomorphism `TF ⊕ TG → T(F ⊕ G)`, `((a, b), (c, d)) ↦ ((a, c), (b, d))`. -/
def tangentProdComm (F G : ScBanach) : ScOperator (F.tangent.prod G.tangent) (F.prod G).tangent where
  lvl m := (ContinuousLinearEquiv.prodProdProdComm ℝ (F (m + 1)) (F m) (G (m + 1)) (G m) :
    _ →L[ℝ] _)
  incl_comm _ _ := rfl

lemma tangentMapWith_pair {f : E 0 → F 0} {g : E 0 → G 0} {Df : E 1 → E 0 →L[ℝ] F 0}
    {Dg : E 1 → E 0 →L[ℝ] G 0} {G₁ : ScNbhdGerm E C} (hf : IsSc0Germ G₁ f) (hg : IsSc0Germ G₁ g) :
    EqOn (tangentMapWith (pairMap f g) fun x => (Df x).prod (Dg x))
      (tangentProdComm F G 0 ∘ pairMap (tangentMapWith f Df) (tangentMapWith g Dg))
      (G₁.tangent.U 0) := by
  intro p hp
  change (levelMap (pairMap f g) 1 p.1, (Df p.1 p.2, Dg p.1 p.2)) =
    ((levelMap f 1 p.1, levelMap g 1 p.1), (Df p.1 p.2, Dg p.1 p.2))
  rw [hf.levelMap_pair hg (G₁.mem_tangent_U.1 hp)]

lemma IsSc1GermWith.pair {G₁ : ScNbhdGerm E C} {f : E 0 → F 0} {g : E 0 → G 0}
    {Df : E 1 → E 0 →L[ℝ] F 0} {Dg : E 1 → E 0 →L[ℝ] G 0} (hf : IsSc1GermWith G₁ f Df)
    (hg : IsSc1GermWith G₁ g Dg) :
    IsSc1GermWith G₁ (pairMap f g) fun x => (Df x).prod (Dg x) where
  isSc0 := hf.isSc0.pair hg.isSc0
  hasFDerivWithinAt x hx := by
    have := (hf.hasFDerivWithinAt x hx).prodMk (hg.hasFDerivWithinAt x hx)
    exact this.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  tangent_isSc0 :=
    (((tangentProdComm F G).isSc0Germ _).comp (hf.tangent_isSc0.pair hg.tangent_isSc0)
      (G₁.tangent.mapsToGerm_full _)).congr (tangentMapWith_pair hf.isSc0 hg.isSc0).symm

/-- The pairing of sc^k-germs is an sc^k-germ. -/
theorem IsSckGerm.pair : ∀ {k : ℕ} {E F G : ScBanach} {C : Set (E 0)} {G₁ : ScNbhdGerm E C}
    {f : E 0 → F 0} {g : E 0 → G 0}, IsQuadrantLike E C → IsSckGerm k G₁ f → IsSckGerm k G₁ g →
    IsSckGerm k G₁ (pairMap f g)
  | 0, _, _, _, _, _, _, _, _, hf, hg => IsSc0Germ.pair hf hg
  | k + 1, _, _, _, _, G₁, f, g, hC, hf, hg => by
    have h1 := hf.1.isSc1GermWith_scDerivGerm.pair hg.1.isSc1GermWith_scDerivGerm
    refine ⟨h1.isSc1Germ, ?_⟩
    have h2 : EqOn (tangentMapGerm G₁ (pairMap f g))
        (tangentProdComm _ _ 0 ∘ pairMap (tangentMapGerm G₁ f) (tangentMapGerm G₁ g))
        (G₁.tangent.U 0) :=
      (IsSc1Germ.tangentMapGerm_eqOn hC h1).trans (tangentMapWith_pair hf.1.isSc0 hg.1.isSc0)
    exact IsSckGerm.congr hC.tangentSet h2.symm
      ((IsSckGerm.pair (k := k) hC.tangentSet hf.2 hg.2).operator_comp hC.tangentSet _)

theorem IsScSmoothGerm.pair {G₁ : ScNbhdGerm E C} {f : E 0 → F 0} {g : E 0 → G 0}
    (hC : IsQuadrantLike E C) (hf : IsScSmoothGerm G₁ f) (hg : IsScSmoothGerm G₁ g) :
    IsScSmoothGerm G₁ (pairMap f g) := fun k => (hf k).pair hC (hg k)

/-! ### Projections -/

/-- The projection `E ⊕ F → E` as an sc-operator. -/
def ScBanach.fstOp (E F : ScBanach) : ScOperator (E.prod F) E where
  lvl m := ContinuousLinearMap.fst ℝ (E m) (F m)
  incl_comm _ _ := rfl

/-- The projection `E ⊕ F → F` as an sc-operator. -/
def ScBanach.sndOp (E F : ScBanach) : ScOperator (E.prod F) F where
  lvl m := ContinuousLinearMap.snd ℝ (E m) (F m)
  incl_comm _ _ := rfl

@[simp] lemma ScBanach.fstOp_apply (E F : ScBanach) (m : ℕ) (p : (E.prod F) m) :
    E.fstOp F m p = p.1 := rfl

@[simp] lemma ScBanach.sndOp_apply (E F : ScBanach) (m : ℕ) (p : (E.prod F) m) :
    E.sndOp F m p = p.2 := rfl

end Polyfold
