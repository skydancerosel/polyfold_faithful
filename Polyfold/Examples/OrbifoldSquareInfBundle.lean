import Polyfold.Examples.OrbifoldSquareBundle
import Polyfold.Examples.WeightedEllTwo
import Polyfold.Chapter4.LocalStrongBundle
import Polyfold.Chapter15.ProductFredholm
import Polyfold.Chapter8.NonVacuityBundle
import Polyfold.Chapter3.TameGermDataStabilization

/-!
# The orbifold `(ℂ × H)/ℤ₅` and the section `(z, e) ↦ (z², e)`: the strong bundle

The infinite-dimensional version of the worked example `ℂ/ℤ₅`, `z ↦ z²`, for Hofer–Wysocki–Zehnder,
*Polyfold and Fredholm Theory* (Springer 2021), Theorem 16.6.6, 2021 p. 739.  `H` is the weighted
`ℓ²` sc-Hilbert space of `WeightedEllTwo.lean`, whose levels are strictly nested.

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquareInf`)

* `PH`: the M-polyfold `H` (one chart); `BH`: the strong bundle `H ◁ H → H` (the fibre over a
  point of level `m` has the levels `H_0 ⊇ … ⊇ H_{m+1}`); `AH`: it over the trivial ep-groupoid.
* **`Ainf = A5 × AH`**: the strong bundle `(ℂ × ℂ) × (H ◁ H) → ℂ × H` over the ep-groupoid
  `(ℤ/5 ⋉ ℂ) × H`, where `ℤ/5` acts on `ℂ` with weight `1`, on the fibre `ℂ` with weight `2`, and
  trivially on `H`.
* `idSec`: the section `e ↦ (e, e)` of `H ◁ H`; **`sqInf`**: the section
  `(z, e) ↦ ((z, z²), (e, e))`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold.Examples.OrbifoldSquareInf

open TrivialBundle EpGroupoid.Examples StrongBundle WeightedEllTwo OrbifoldSquare SBLocalization

/-- `H₀` is relatively open in the partial quadrant `H₀`. -/
theorem relOpen_H : IsRelOpenInQuadrant H (univ : Set (H 0)) univ := Stabilize.relOpenUniv H

/-- The points of `H`, as the domain of its one chart. -/
abbrev HObj : Type := ↥(univ : Set (H 0))

/-- The point `0` of `H`. -/
def h0 : HObj := ⟨0, mem_univ _⟩

/-- The point `e` of `H`. -/
def hpt (e : H 0) : HObj := ⟨e, mem_univ _⟩

@[simp] theorem hpt_val (e : H 0) : ((hpt e : HObj) : H 0) = e := rfl

/-- **The M-polyfold `H`** (one chart, the identity). -/
abbrev PH : MPolyfold HObj := LocalBundle.basePolyfold relOpen_H h0

/-- **The strong bundle `H ◁ H → H`**. -/
abbrev BH : StrongBundle PH (LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H)) :=
  LocalBundle.bundle H relOpen_H h0

/-- `H ◁ H → H` over the trivial ep-groupoid of `H`. -/
def AH : SEP.{0} :=
  ⟨_, _, EpGroupoid.trivial PH, _, LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H), BH,
    EpStrongBundle.trivial BH⟩

/-- **`(ℂ × ℂ) × (H ◁ H) → ℂ × H` over `(ℤ/5 ⋉ ℂ) × H`.** -/
abbrev Ainf : SEP.{0} := A5.prod AH

/-- The section `e ↦ (e, e)` of `H ◁ H → H`. -/
abbrev idSec : AH.Obj → AH.W := LocalBundle.sec (E := H) (U := (univ : Set (H 0))) (F := H) id

theorem idSec_apply (x : HObj) : idSec x = (x, (x : H 0)) := rfl

/-- **The section `f(z, e) = ((z, z²), (e, e))`.** -/
abbrev sqInf : Ainf.Obj → Ainf.W := Prod.map sqSection idSec

theorem sqInf_apply (x : Ainf.Obj) : sqInf x = (sqSection x.1, idSec x.2) := rfl

end Polyfold.Examples.OrbifoldSquareInf
