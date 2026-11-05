import Polyfold
/-! Blind formalization of V5_14 (the text's §5.2, proof of Corollary 5.8, p. 173): "It is a
priori clear that `f^i` is sc-Fredholm", as a section of `P^i : Y^i → X^i` (item title: the
shifted strong bundle `P¹`, and `f¹` sc-Fredholm on it).

Choices:
- Setting: spaces in `Type` (`X Y : Type`).  A strong bundle `P : Y → X` over an M-polyfold
  `PX : MPolyfold X` is the project's `StrongBundle PX P` (Definition 2.51; fibrewise linear
  structure as instances on the fibres `P⁻¹(x)`, `Y` paracompact Hausdorff), bundled together
  with a section `f : X → Y` in the structure `Data` below.
- `f` sc-Fredholm: the project's `StrongBundle.IsScFredholmSection` (Definition 3.14, germ reading:
  sc-smooth, regularizing, an sc-Fredholm germ at every smooth point), the notion used throughout
  §5.2.  I did not use the tame-chart variant (Definition 3.51).
- `P^i`, `X^i`, `f^i` (never defined in the text; "raising the index"): `X^i` has levels
  `X_{m+i}`, `Y^i` has double levels `Y_{m+i,k+i}`, `f^i = f|X_i`.  I take the project's `i = 1`
  construction — `MPolyfold.shift` on `PX.Level 1` (the M-polyfold `X¹`), `StrongBundle.shift`
  (`P¹ : Y¹ → X¹` with `Y¹ = Y_{1,1}` in the level topology of `Y[0]`, atlas of index raises, so
  `(Y¹)_{m,k} = Y_{m+1,k+1}` per its docstring), `StrongBundle.sectionShift` (`f¹(x) = f(x)`;
  junk value the fibre zero when `f(x) ∉ Y_{1,1}`, which never happens for sc-smooth `f`) — and
  iterate it: `P^{i+1} = (P^i)¹`, `f^{i+1} = (f^i)¹` (`Data.iter`).  I trusted these definitions
  from their docstrings (signatures checked); `i = 0` gives `P`, `f` themselves.
- Generality: the claim is stated for every `i : ℕ`.  Over all strong bundles this is equivalent
  to the `i = 1` case of the title (induction, the class of bundles being closed under the shift).
- Hypotheses: "a priori" is read as "from `f` sc-Fredholm alone", so B assumes neither the
  tameness of `X` nor the compactness of `f⁻¹(0)` from the statement of Corollary 5.8 (the
  in-context reading with those two hypotheses added would be weaker).  I believe the claim is
  true in this generality (fillers, sc⁺-sections, basic germs and regularity all survive the
  index raise).
-/
namespace RoundTrip.V5_14_r2
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

/-- Corollary 5.8, proof: if `f` is an sc-Fredholm section of `P : Y → X`, then for every `i`
the section `f^i` of `P^i : Y^i → X^i` is sc-Fredholm. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    Bd.IsScFredholmSection f →
      ∀ i : ℕ,
        let D : Data := { X := X, PX := PX, Y := Y, P := P, Bd := Bd, f := f }
        (D.iter i).Bd.IsScFredholmSection (D.iter i).f

end RoundTrip.V5_14_r2
