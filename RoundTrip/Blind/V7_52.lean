import Polyfold
/-! Blind formalization of V7_52 (the 2017 book's Part II, §7.3, Proposition 7.11, p. 247,
proof p. 248: index lifting).

Text: if `X = (X, 𝐗)` is an ep-groupoid, then so is `X¹ = (X¹, 𝐗¹)`; if `X` is tame, so is
`X¹`.

Choices:
- Setting as in `RoundTrip/Blind/V7_49.lean`: `Obj Mor : Type` (universe 0) with the instances
  of the project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's ep-groupoid,
  Definition 7.3, fields read with `#print`).
- `X¹ = (X¹, 𝐗¹)` (my `IsLiftB X Y`): an ep-groupoid `Y` whose object space is the level `X_1`
  and whose morphism space is the level `𝐗_1` — the project's types `X.PObj.Level 1`,
  `X.PMor.Level 1` with their level topologies (the paragraph after Definition 2.14; Hausdorff
  and paracompact by the project's instances, Theorem 2.16) — such that
  (a) the M-polyfold structures of `Y` are those of `X¹` and `𝐗¹`: the atlas of `Y.PObj` is
      equivalent (Definition 2.12, `MAtlas.Equiv`) to that of the project's `X.PObj.shift` (the
      M-polyfold `X¹` with the level charts `(V₁, φ, (O₁, C₁, E¹))`), and likewise for `PMor`;
      equivalence, not equality, since an M-polyfold structure is an equivalence class of atlases;
  (b) the structure maps of `Y` are those of `X` restricted to level 1: `s, t, u, ι` commute with
      the inclusions `X_1 → X`, `𝐗_1 → 𝐗` (`levelVal 1`), and so does `m` on composable pairs
      (`s φ = t ψ`; off them the project's `comp` is a junk value, so nothing is asked).
  (b) includes that `s, t, u, ι, m` preserve level 1.
- "`X¹` is an ep-groupoid": there is such a `Y` (an `EpGroupoid`, i.e. (1)–(4) of
  Definition 7.3 hold for `X¹`).  "If `X` is tame so is `X¹`": for that `Y`, `X.IsTame → Y.IsTame`
  (the project's `EpGroupoid.IsTame`, checked with `#print`: the object M-polyfold is tame,
  Definition 7.6 / 2.37).  Up to the junk values of `m` and the choice of atlas in the class, `Y` is
  unique, so the existential reading loses nothing.
- I trust the project's `MPolyfold.shift` as the text's `X¹` (its docstring; it is a Chapter 2
  definition, used as `X¹` in the earlier blind files on levels).
- Nothing looks false to me.
-/
namespace RoundTrip.V7_52
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `Y` is the ep-groupoid `X¹ = (X¹, 𝐗¹)`: the M-polyfolds `X¹`, `𝐗¹` (up to equivalence of
atlases) and the structure maps of `X` restricted to level `1`. -/
def IsLiftB (X : EpGroupoid Obj Mor) (Y : EpGroupoid (X.PObj.Level 1) (X.PMor.Level 1)) :
    Prop :=
  Y.PObj.atlas.Equiv X.PObj.shift.atlas ∧
  Y.PMor.atlas.Equiv X.PMor.shift.atlas ∧
  (∀ φ : X.PMor.Level 1, X.PObj.levelVal 1 (Y.src φ) = X.src (X.PMor.levelVal 1 φ)) ∧
  (∀ φ : X.PMor.Level 1, X.PObj.levelVal 1 (Y.tgt φ) = X.tgt (X.PMor.levelVal 1 φ)) ∧
  (∀ x : X.PObj.Level 1, X.PMor.levelVal 1 (Y.unit x) = X.unit (X.PObj.levelVal 1 x)) ∧
  (∀ φ : X.PMor.Level 1, X.PMor.levelVal 1 (Y.inv φ) = X.inv (X.PMor.levelVal 1 φ)) ∧
  (∀ φ ψ : X.PMor.Level 1, Y.src φ = Y.tgt ψ →
    X.PMor.levelVal 1 (Y.comp φ ψ) = X.comp (X.PMor.levelVal 1 φ) (X.PMor.levelVal 1 ψ))

end

/-- Proposition 7.11: `X¹` is an ep-groupoid, tame if `X` is. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor),
    ∃ Y : EpGroupoid (X.PObj.Level 1) (X.PMor.Level 1), IsLiftB X Y ∧ (X.IsTame → Y.IsTame)

end RoundTrip.V7_52
