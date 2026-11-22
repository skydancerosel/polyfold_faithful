import Polyfold.Chapter17.GroupoidalCategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 745–746): **Definition 17.1.5** (the transition set `M(Ψ, Ψ')`) and its structure maps
`s, t, u, ι, m` (p. 746), for arbitrary maps into the objects of a groupoid.  The same set and
maps are used in §19.1 (pp. 865–866).  Numbers and pages are the 2021 text's.

# Transition sets

## The text, paraphrased

(Definition 17.1.5, p. 745) The transition set `M(Ψ, Ψ')` of two local uniformizers is the weak
fibred product of `O → C ← O'`: all tuples `(q, φ, q') ∈ O × C × O'` with `φ : Ψ(q) → Ψ'(q')`.
(p. 746) Its structure maps: (1) `s(q, φ, q') = q`; (2) `t(q, φ, q') = q'`; (3) the unit map
`O → M(Ψ, Ψ)`, `q ↦ (q, 1_{Ψ(q)}, q)`; (4) the inversion `M(Ψ, Ψ') → M(Ψ', Ψ)`,
`(q, φ, q') ↦ (q', φ⁻¹, q)`; (5) the multiplication
`m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')`, `m((q', φ', q''), (q, φ, q')) = (q, φ' ∘ φ, q'')`.

## What is formalized (namespace `Polyfold.GroupoidStr.TransitionSet`)

* `GroupoidStr.TransitionSet G f f'` (**Definition 17.1.5**) for a groupoid `G` and arbitrary maps
  `f : O → Obj`, `f' : O' → Obj` (for uniformizers, `f = Ψ` and `f' = Ψ'` on objects): the tuples
  `(src, mor, tgt)` with `mor : f(src) → f'(tgt)`; `TransitionSet.ext`;
  `equivWeakFibredProduct` (the literal set of tuples in `O × Mor × O'`).
* The structure maps (p. 746): the fields `src`, `tgt` ((1), (2)), `unit` ((3)), `inv` ((4)),
  `comp` (the composite `(q, φ' ∘ φ, q'')` of two tuples whose morphisms are composable) and
  `mul` ((5), on the fibred product `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`, `MPolyfold.fibredProduct src tgt`).
* Their laws: `src_unit`, `tgt_unit`, `src_inv`, `tgt_inv`, `src_comp`, `tgt_comp`, `inv_inv`,
  `inv_unit`, `comp_assoc`, `comp_unit`, `unit_comp`, `comp_inv`, `inv_comp`, `mul_eq_comp`.

## Readings

* The transition set is defined for maps into the objects of any groupoid, without any topology
  or M-polyfold structure, so that it serves Definition 17.1.5 and §19.1 alike.
* The tuple is a structure with fields `src = q`, `mor = φ`, `tgt = q'`;
  `equivWeakFibredProduct` identifies it with the text's subset of `O × Mor × O'`.
* `comp` needs only that the morphisms are composable in `G`, so it composes tuples of
  `M(Ψ', Ψ'')` and `M(Ψ, Ψ'₂)` with different middle maps; `mul` is the text's `m`, where
  `s(q', φ', q'') = t(q, φ, q')` gives composability.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u v

namespace GroupoidStr

variable {Obj Mor : Type u} (G : GroupoidStr Obj Mor)

/-- **2021 Definition 17.1.5, p. 745**: the **transition set** `M(f, f')`, the weak fibred product
of `O → Obj ← O'`: the tuples `(q, φ, q')` with `φ : f(q) → f'(q')`.  For local uniformizers
`Ψ, Ψ'` it is `M(Ψ, Ψ')`. -/
@[ext]
structure TransitionSet {O O' : Type v} (f : O → Obj) (f' : O' → Obj) where
  /-- The source `s(q, φ, q') = q` (p. 746 (1)). -/
  src : O
  /-- The morphism `φ`. -/
  mor : Mor
  /-- The target `t(q, φ, q') = q'` (p. 746 (2)). -/
  tgt : O'
  src_mor : G.src mor = f src
  tgt_mor : G.tgt mor = f' tgt

namespace TransitionSet

variable {G} {O O' O₁ O₂ O₂' O₃ : Type v} {f : O → Obj} {f' : O' → Obj} {f₁ : O₁ → Obj}
  {f₂ : O₂ → Obj} {f₂' : O₂' → Obj} {f₃ : O₃ → Obj}

variable (G f f') in
/-- **Definition 17.1.5, literally**: the transition set is the set of tuples
`(q, φ, q') ∈ O × Mor × O'` with `φ : f(q) → f'(q')`. -/
def equivWeakFibredProduct :
    G.TransitionSet f f' ≃ {p : O × Mor × O' // G.src p.2.1 = f p.1 ∧ G.tgt p.2.1 = f' p.2.2} where
  toFun a := ⟨(a.src, a.mor, a.tgt), a.src_mor, a.tgt_mor⟩
  invFun p := ⟨p.1.1, p.1.2.1, p.1.2.2, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem mor_mem_mor (a : G.TransitionSet f f') : a.mor ∈ G.mor (f a.src) (f' a.tgt) :=
  ⟨a.src_mor, a.tgt_mor⟩

/-- **The unit map** `O → M(Ψ, Ψ)`, `q ↦ (q, 1_{f(q)}, q)` (p. 746 (3)). -/
def unit (q : O) : G.TransitionSet f f :=
  ⟨q, G.unit (f q), q, G.src_unit _, G.tgt_unit _⟩

/-- **The inversion map** `M(Ψ, Ψ') → M(Ψ', Ψ)`, `(q, φ, q') ↦ (q', φ⁻¹, q)` (p. 746 (4)). -/
def inv (a : G.TransitionSet f f') : G.TransitionSet f' f :=
  ⟨a.tgt, G.inv a.mor, a.src, (G.src_inv _).trans a.tgt_mor, (G.tgt_inv _).trans a.src_mor⟩

/-- The composite `(q, φ' ∘ φ, q'')` of `(q', φ', q'')` and `(q, φ, q'₂)` with composable
morphisms (the multiplication of p. 746 (5), without fixing the middle map). -/
def comp (a : G.TransitionSet f₂ f₃) (b : G.TransitionSet f₁ f₂')
    (h : G.src a.mor = G.tgt b.mor) : G.TransitionSet f₁ f₃ :=
  ⟨b.src, G.comp a.mor b.mor, a.tgt, (G.src_comp _ _ h).trans b.src_mor,
    (G.tgt_comp _ _ h).trans a.tgt_mor⟩

theorem mor_composable_of_src_eq_tgt {a : G.TransitionSet f₂ f₃} {b : G.TransitionSet f₁ f₂}
    (h : a.src = b.tgt) : G.src a.mor = G.tgt b.mor := by
  rw [a.src_mor, b.tgt_mor, h]

/-- **The multiplication** `m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')`,
`m((q', φ', q''), (q, φ, q')) = (q, φ' ∘ φ, q'')` (p. 746 (5)). -/
def mul (p : MPolyfold.fibredProduct (TransitionSet.src : G.TransitionSet f₂ f₃ → O₂)
    (TransitionSet.tgt : G.TransitionSet f₁ f₂ → O₂)) : G.TransitionSet f₁ f₃ :=
  comp p.1.1 p.1.2 (mor_composable_of_src_eq_tgt p.2)

/-! ### The laws of the structure maps -/

@[simp] theorem src_unit (q : O) : (unit q : G.TransitionSet f f).src = q := rfl
@[simp] theorem tgt_unit (q : O) : (unit q : G.TransitionSet f f).tgt = q := rfl
@[simp] theorem mor_unit (q : O) : (unit q : G.TransitionSet f f).mor = G.unit (f q) := rfl
@[simp] theorem src_inv (a : G.TransitionSet f f') : a.inv.src = a.tgt := rfl
@[simp] theorem tgt_inv (a : G.TransitionSet f f') : a.inv.tgt = a.src := rfl
@[simp] theorem mor_inv (a : G.TransitionSet f f') : a.inv.mor = G.inv a.mor := rfl

@[simp] theorem src_comp (a : G.TransitionSet f₂ f₃) (b : G.TransitionSet f₁ f₂')
    (h : G.src a.mor = G.tgt b.mor) : (comp a b h).src = b.src := rfl

@[simp] theorem tgt_comp (a : G.TransitionSet f₂ f₃) (b : G.TransitionSet f₁ f₂')
    (h : G.src a.mor = G.tgt b.mor) : (comp a b h).tgt = a.tgt := rfl

@[simp] theorem mor_comp (a : G.TransitionSet f₂ f₃) (b : G.TransitionSet f₁ f₂')
    (h : G.src a.mor = G.tgt b.mor) : (comp a b h).mor = G.comp a.mor b.mor := rfl

theorem mul_eq_comp (p : MPolyfold.fibredProduct (TransitionSet.src : G.TransitionSet f₂ f₃ → O₂)
    (TransitionSet.tgt : G.TransitionSet f₁ f₂ → O₂)) :
    mul p = comp p.1.1 p.1.2 (mor_composable_of_src_eq_tgt p.2) := rfl

@[simp] theorem inv_inv (a : G.TransitionSet f f') : a.inv.inv = a :=
  TransitionSet.ext rfl (G.inv_inv _) rfl

@[simp] theorem inv_unit (q : O) : (unit q : G.TransitionSet f f).inv = unit q :=
  TransitionSet.ext rfl (G.inv_unit _) rfl

theorem comp_assoc {O₃' O₄ : Type v} {f₃' : O₃' → Obj} {f₄ : O₄ → Obj}
    (a : G.TransitionSet f₃ f₄) (b : G.TransitionSet f₂ f₃') (c : G.TransitionSet f₁ f₂')
    (hab : G.src a.mor = G.tgt b.mor) (hbc : G.src b.mor = G.tgt c.mor) :
    comp (comp a b hab) c (by rw [mor_comp, G.src_comp _ _ hab, hbc]) =
      comp a (comp b c hbc) (by rw [mor_comp, G.tgt_comp _ _ hbc, hab]) :=
  TransitionSet.ext rfl (G.comp_assoc _ _ _ hab hbc) rfl

theorem comp_unit (a : G.TransitionSet f f') :
    comp a (unit a.src : G.TransitionSet f f) (by rw [mor_unit, G.tgt_unit, a.src_mor]) = a :=
  TransitionSet.ext rfl (GroupoidStr.comp_unit_of_eq a.src_mor) rfl

theorem unit_comp (a : G.TransitionSet f f') :
    comp (unit a.tgt : G.TransitionSet f' f') a (by rw [mor_unit, G.src_unit, a.tgt_mor]) = a :=
  TransitionSet.ext rfl (GroupoidStr.unit_comp_of_eq a.tgt_mor) rfl

theorem comp_inv (a : G.TransitionSet f f') :
    comp a a.inv (by rw [mor_inv, G.tgt_inv]) = unit a.tgt :=
  TransitionSet.ext rfl ((G.comp_inv _).trans (congrArg G.unit a.tgt_mor)) rfl

theorem inv_comp (a : G.TransitionSet f f') :
    comp a.inv a (by rw [mor_inv, G.src_inv]) = unit a.src :=
  TransitionSet.ext rfl ((G.inv_comp _).trans (congrArg G.unit a.src_mor)) rfl

theorem inv_comp_rev (a : G.TransitionSet f₂ f₃) (b : G.TransitionSet f₁ f₂')
    (h : G.src a.mor = G.tgt b.mor) :
    (comp a b h).inv = comp b.inv a.inv (by rw [mor_inv, mor_inv, G.src_inv, G.tgt_inv, h]) :=
  TransitionSet.ext rfl (G.inv_comp_rev h) rfl

end TransitionSet

end GroupoidStr

end Polyfold
