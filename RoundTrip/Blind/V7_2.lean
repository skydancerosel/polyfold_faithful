import Polyfold
/-! Blind formalization of V7_2 (the text's Part II, §7.1, Definition 7.2, p. 226 of the 2017
book).

Text: for fixed `x ∈ X`, the isotropy group (stabilizer group) of `x` is
`G_x = {φ ∈ 𝐗 | φ : x → x}`.

Choices:
- This item is a definition.  Setting: a groupoid in the project's sense, `G : GroupoidStr Obj Mor`
  with `Obj Mor : Type` (universe 0); `GroupoidStr` is characterized as the text's groupoid of
  Definition 7.1 in `RoundTrip/Blind/V7_1.lean`.  The statement is purely algebraic, so it is
  made for every groupoid (an ep-groupoid's `G_x` is that of its underlying `GroupoidStr`).
- `G_x` as a set: `isoSetB G x = {φ | s φ = x ∧ t φ = x}`.
- "group": the text calls `G_x` a group without naming the operation; I read it as the group
  under the groupoid composition, `g · h = g ∘ h` (first `h`, then `g`), with unit `1_x` and
  inverse `ι`.  B asserts that this set is closed under these operations (so that it is a group:
  the group laws are those of the groupoid), and that the project's `GroupoidStr.Isotropy x`
  (fields read with `#print`: a morphism `val` with `s val = x`, `t val = x`) with its group
  instance (found by `#synth`, not opened) is this group: `val` is injective with range
  `isoSetB G x`, and `val` turns `*`, `1`, `⁻¹` into `∘`, `1_x`, `ι`.  (Had the project used the
  opposite order `g · h = h ∘ g`, the conjunct on `*` would fail; both conventions give
  isomorphic groups.)
- Nothing looks false to me.
-/
namespace RoundTrip.V7_2
open Polyfold

/-- `G_x = {φ ∈ 𝐗 | φ : x → x}`. -/
def isoSetB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (x : Obj) : Set Mor :=
  {φ | G.src φ = x ∧ G.tgt φ = x}

/-- Definition 7.2: `G_x` is a group under composition, and the project's `Isotropy x` is that
group. -/
def B : Prop :=
  ∀ (Obj Mor : Type) (G : GroupoidStr Obj Mor) (x : Obj),
    -- `G_x` is a group under composition, unit `1_x`, inverse `ι`
    (∀ g ∈ isoSetB G x, ∀ h ∈ isoSetB G x, G.comp g h ∈ isoSetB G x) ∧
    G.unit x ∈ isoSetB G x ∧
    (∀ g ∈ isoSetB G x, G.inv g ∈ isoSetB G x) ∧
    -- the project's `Isotropy x` is `G_x` with this group structure
    Function.Injective (GroupoidStr.Isotropy.val : G.Isotropy x → Mor) ∧
    Set.range (GroupoidStr.Isotropy.val : G.Isotropy x → Mor) = isoSetB G x ∧
    (∀ g h : G.Isotropy x, (g * h).val = G.comp g.val h.val) ∧
    (1 : G.Isotropy x).val = G.unit x ∧
    (∀ g : G.Isotropy x, g⁻¹.val = G.inv g.val)

end RoundTrip.V7_2
