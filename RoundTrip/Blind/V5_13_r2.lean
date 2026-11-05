import Polyfold
/-! Blind formalization of V5_13 (the text's §5.2, Corollary 5.8, p. 173): over a tame `X`, if
`f⁻¹(0)` is compact, then `f^i` is an sc-Fredholm section of `P^i : Y^i → X^i` with compact
solution set.

Choices:
- Setting: spaces in `Type` (`X Y : Type`).  A strong bundle `P : Y → X` over an M-polyfold
  `PX : MPolyfold X` is the project's `StrongBundle PX P` (Definition 2.51; fibrewise linear
  structure as instances on the fibres `P⁻¹(x)`, `Y` paracompact Hausdorff), bundled together
  with a section `f : X → Y` in the structure `Data` below.
- "Over a tame `X`": `PX.IsTame` (Definition 2.37: an equivalent atlas of tame charts, a property
  of the given structure); the bundle is not assumed tame.
- `f` sc-Fredholm (the standing hypothesis of §5.2, implicit in the quoted statement and clearly
  presupposed, since `f^i` is to be sc-Fredholm): the project's `StrongBundle.IsScFredholmSection`
  (Definition 3.14, germ reading: sc-smooth, regularizing, an sc-Fredholm germ at every smooth
  point).  I did not use the tame-chart variant (Definition 3.51).
- `f⁻¹(0) = {x | f(x) = 0_x}` (`Data.zeroSet`, my own definition: `f x` equals the zero of the
  fibre `P⁻¹(x)` seen in `Y`); "compact" = `IsCompact` in `X = X_0`.  The solution set of `f^i` is
  the same definition for `P^i`, `f^i`, and its compactness is taken in `X^i` (the type
  `X_i`, with the level topology of the iterated `MPolyfold.Level 1`).
- `P^i`, `X^i`, `f^i` (never defined in the text; "raising the index"): `X^i` has levels
  `X_{m+i}`, `Y^i` has double levels `Y_{m+i,k+i}`, `f^i = f|X_i`.  I take the project's `i = 1`
  construction — `MPolyfold.shift` on `PX.Level 1` (the M-polyfold `X¹`), `StrongBundle.shift`
  (`P¹ : Y¹ → X¹` with `Y¹ = Y_{1,1}` in the level topology of `Y[0]`, atlas of index raises, so
  `(Y¹)_{m,k} = Y_{m+1,k+1}` per its docstring), `StrongBundle.sectionShift` (`f¹(x) = f(x)`;
  junk value the fibre zero when `f(x) ∉ Y_{1,1}`, which never happens for sc-smooth `f`) — and
  iterate it: `P^{i+1} = (P^i)¹`, `f^{i+1} = (f^i)¹` (`Data.iter`).  I trusted these definitions
  from their docstrings (signatures checked).
- Quantifier: every `i : ℕ` (`i = 0` is the hypothesis itself).  B is the conjunction, for each
  `i`, of "`f^i` is sc-Fredholm" and "`(f^i)⁻¹(0)` is compact in `X^i`".
- Nothing looks false to me (by Theorem 5.7 `f⁻¹(0) ⊆ X_∞` is compact in every `X_i`).
-/
namespace RoundTrip.V5_13_r2
open Polyfold

/-- A strong bundle `P : Y → X` over an M-polyfold, with a map `f : X → Y` (a candidate
section). -/
structure Data : Type 1 where
  X : Type
  [tX : TopologicalSpace X]
  [t2X : T2Space X]
  [pcX : ParacompactSpace X]
  PX : MPolyfold X
  Y : Type
  [tY : TopologicalSpace Y]
  [t2Y : T2Space Y]
  [pcY : ParacompactSpace Y]
  P : Y → X
  [grp : ∀ x : X, AddCommGroup (P ⁻¹' {x})]
  [mdl : ∀ x : X, Module ℝ (P ⁻¹' {x})]
  Bd : StrongBundle PX P
  f : X → Y

attribute [instance] Data.tX Data.t2X Data.pcX Data.tY Data.t2Y Data.pcY Data.grp Data.mdl

/-- The index raise by one: `P¹ : Y¹ → X¹` with the section `f¹` (project constructions). -/
noncomputable def Data.shift (D : Data) : Data where
  X := D.PX.Level 1
  PX := D.PX.shift
  Y := D.Bd.ShiftSpace
  P := D.Bd.shiftProj
  Bd := D.Bd.shift
  f := D.Bd.sectionShift D.f

/-- The index raise by `i`: `P^i : Y^i → X^i` with the section `f^i`. -/
noncomputable def Data.iter (D : Data) : ℕ → Data
  | 0 => D
  | i + 1 => (D.iter i).shift

/-- The solution set `f⁻¹(0) = {x | f(x) = 0 ∈ P⁻¹(x)}`. -/
def Data.zeroSet (D : Data) : Set D.X :=
  {x | D.f x = ((0 : D.P ⁻¹' {x}) : D.Y)}

/-- Corollary 5.8: over a tame M-polyfold, if the sc-Fredholm section `f` has compact solution
set, then for every `i` the section `f^i` of `P^i : Y^i → X^i` is sc-Fredholm and its solution
set is compact (in `X^i`). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    let D : Data := { X := X, PX := PX, Y := Y, P := P, Bd := Bd, f := f }
    PX.IsTame → Bd.IsScFredholmSection f → IsCompact D.zeroSet →
      ∀ i : ℕ,
        (D.iter i).Bd.IsScFredholmSection (D.iter i).f ∧ IsCompact (D.iter i).zeroSet

end RoundTrip.V5_13_r2
