import Polyfold
/-! Blind formalization of V7_1 (the text's Part II, §7.1, Definition 7.1 and the paragraph after
it, pp. 225–226 of the 2017 book).

Text: a groupoid `X = (X, 𝐗)` is a small category with object set `X`, morphism set `𝐗`, all
morphisms invertible, given by five structure maps `(s, t, m, u, ι)`: (1) source and target
`s, t : 𝐗 → X`; (2) an associative multiplication `m(φ, ψ) = φ ∘ ψ` on the fibred product
`𝐗 ₛ×ₜ 𝐗 = {(φ, ψ) | s(φ) = t(ψ)}` with `φ ∘ ψ : x → y` for `ψ : x → z`, `φ : z → y`; (3) units
`1_x : x → x`, two-sided for the composition, forming `u : X → 𝐗`; (4) two-sided inverses
`φ⁻¹ : y → x` of `φ : x → y`, forming `ι : 𝐗 → 𝐗`.  After it: `mor(x, y) = {φ | s φ = x, t φ = y}`;
`x ∼ y` iff there is a morphism `φ : x → y`; `|X| = X/∼`, `|x| = {y | y ∼ x}`, `π(x) = |x|`.

Choices:
- This item is a definition.  Setting: object and morphism sets `Obj Mor : Type` (universe 0;
  the project's `GroupoidStr` is universe-polymorphic with both in one universe `u`, this is
  `u = 0`).  "Small category" = the objects and morphisms form sets (types); nothing else.
- My notion of the text's groupoid, `IsGroupoidB s t m u ι`, from Mathlib-free data: the
  multiplication `m` is a function on the fibred product, i.e. on the subtype
  `{p : Mor × Mor // s p.1 = t p.2}` (`ComposableB s t`), exactly as the text has it (not a total
  map with junk values).  The axioms: `s(φ∘ψ) = s ψ`, `t(φ∘ψ) = t φ` (the typing in (2));
  associativity for composable triples; `s(1_x) = t(1_x) = x`, `φ ∘ 1_x = φ` for `s φ = x` and
  `1_x ∘ ψ = ψ` for `t ψ = x`; `s(φ⁻¹) = t φ`, `t(φ⁻¹) = s φ`, `φ ∘ φ⁻¹ = 1_y`, `φ⁻¹ ∘ φ = 1_x`.
  The text says "there exists" a unit / an inverse and that "these define" `u`, `ι`; since the
  structure maps are part of the data, I take `u`, `ι` as given maps.
- Project definitions characterized (fields read with `#print`): `GroupoidStr Obj Mor` (total
  `comp : Mor → Mor → Mor` whose laws are asked on composable pairs only).  B (a): the structure
  maps of every `GroupoidStr`, with `comp` restricted to the fibred product, form a text groupoid;
  (b): every text groupoid is (with the same `s, t, u, ι`, and `comp = m` on composable pairs)
  a `GroupoidStr`.  `mor(x, y)` is the project's `GroupoidStr.mor` (c).
- "the equivalence relation `x ∼ y`" presupposes that `∼` is an equivalence relation: asserted
  (d) for my `relB` (`∃ φ, s φ = x ∧ t φ = y`), together with: the project's
  `GroupoidStr.Isomorphic` is `relB`.
- The orbit space (e): the project's `OrbitSpace` (a quotient type) with `π` is, up to a
  bijection, the set of classes `|x| = {y | y ∼ x}` with `π(x) = |x|`: there is a bijection
  `e : |X| ≃ {S : Set Obj | ∃ x, S = |x|}` with `e (π x) = |x|` for all `x`.  No topology enters
  here (this is the purely algebraic groupoid).
- Nothing looks false to me.
-/
namespace RoundTrip.V7_1
open Polyfold

/-- The fibred product `𝐗 ₛ×ₜ 𝐗 = {(φ, ψ) | s(φ) = t(ψ)}`, as a type. -/
def ComposableB {Obj Mor : Type} (s t : Mor → Obj) : Type :=
  {p : Mor × Mor // s p.1 = t p.2}

/-- **Definition 7.1**: `(s, t, m, u, ι)` are the structure maps of a groupoid, with the
multiplication `m` defined on the fibred product `𝐗 ₛ×ₜ 𝐗`. -/
def IsGroupoidB {Obj Mor : Type} (s t : Mor → Obj) (m : ComposableB s t → Mor) (u : Obj → Mor)
    (ι : Mor → Mor) : Prop :=
  -- (2) `ψ : x → z`, `φ : z → y` give `φ ∘ ψ : x → y`
  (∀ p : ComposableB s t, s (m p) = s p.1.2 ∧ t (m p) = t p.1.1) ∧
  -- (2) associativity `(φ ∘ ψ) ∘ χ = φ ∘ (ψ ∘ χ)` for composable triples
  (∀ (φ ψ χ : Mor) (h₁ : s φ = t ψ) (h₂ : s ψ = t χ) (h₃ : s (m ⟨(φ, ψ), h₁⟩) = t χ)
      (h₄ : s φ = t (m ⟨(ψ, χ), h₂⟩)),
      m ⟨(m ⟨(φ, ψ), h₁⟩, χ), h₃⟩ = m ⟨(φ, m ⟨(ψ, χ), h₂⟩), h₄⟩) ∧
  -- (3) units `1_x : x → x`, two-sided
  (∀ x : Obj, s (u x) = x ∧ t (u x) = x) ∧
  (∀ (x : Obj) (φ : Mor) (h : s φ = t (u x)), s φ = x → m ⟨(φ, u x), h⟩ = φ) ∧
  (∀ (x : Obj) (ψ : Mor) (h : s (u x) = t ψ), t ψ = x → m ⟨(u x, ψ), h⟩ = ψ) ∧
  -- (4) inverses `φ⁻¹ : y → x` of `φ : x → y`, two-sided
  (∀ φ : Mor, s (ι φ) = t φ ∧ t (ι φ) = s φ) ∧
  (∀ (φ : Mor) (h : s φ = t (ι φ)), m ⟨(φ, ι φ), h⟩ = u (t φ)) ∧
  (∀ (φ : Mor) (h : s (ι φ) = t φ), m ⟨(ι φ, φ), h⟩ = u (s φ))

/-- `x ∼ y`: there is a morphism `φ : x → y`. -/
def relB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (x y : Obj) : Prop :=
  ∃ φ : Mor, G.src φ = x ∧ G.tgt φ = y

/-- The class `|x| = {y ∈ X | y ∼ x}`. -/
def classB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (x : Obj) : Set Obj :=
  {y | relB G y x}

/-- Definition 7.1: the project's `GroupoidStr` is exactly the text's groupoid; `mor(x, y)`,
`∼`, `|X| = X/∼`, `|x|` and `π` are the text's. -/
def B : Prop :=
  -- (a) every `GroupoidStr` is a groupoid in the text's sense
  (∀ (Obj Mor : Type) (G : GroupoidStr Obj Mor),
    IsGroupoidB G.src G.tgt (fun p => G.comp p.1.1 p.1.2) G.unit G.inv) ∧
  -- (b) every groupoid in the text's sense is a `GroupoidStr`
  (∀ (Obj Mor : Type) (s t : Mor → Obj) (m : ComposableB s t → Mor) (u : Obj → Mor)
      (ι : Mor → Mor), IsGroupoidB s t m u ι →
      ∃ G : GroupoidStr Obj Mor, G.src = s ∧ G.tgt = t ∧ G.unit = u ∧ G.inv = ι ∧
        ∀ p : ComposableB s t, G.comp p.1.1 p.1.2 = m p) ∧
  -- (c) `mor(x, y) = {φ | s(φ) = x, t(φ) = y}`
  (∀ (Obj Mor : Type) (G : GroupoidStr Obj Mor) (x y : Obj),
    G.mor x y = {φ | G.src φ = x ∧ G.tgt φ = y}) ∧
  -- (d) `∼` is an equivalence relation, and it is the project's `Isomorphic`
  (∀ (Obj Mor : Type) (G : GroupoidStr Obj Mor),
    Equivalence (relB G) ∧ ∀ x y : Obj, G.Isomorphic x y ↔ relB G x y) ∧
  -- (e) `|X|` is the set of classes `|x|`, and `π(x) = |x|`
  (∀ (Obj Mor : Type) (G : GroupoidStr Obj Mor),
    ∃ e : G.OrbitSpace ≃ {S : Set Obj // ∃ x, S = classB G x},
      ∀ x : Obj, (e (G.π x)).1 = classB G x)

end RoundTrip.V7_1
