import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_53

/-!
Round trip for V5_53 (Proposition 5.35 and the §5.3 remark "this is the case if `X` is built on
sc-Hilbert spaces").

`A` is the conjunction of the types of the three listed theorems
`Polyfold.LocalModel.hasBumpProperty_of_quadratic`, `Polyfold.proposition_5_35` (no universe
parameters) and `Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert` (universe instantiated at `0`).

* `A → B` (proved, using `A`): `proposition_5_35` gives the project's (pointwise, `f(x) ≠ 0`)
  bump property for a Hilbert `E₀` (B's `IsHilbertNormB` gives `‖v‖² = b(v, v)`; B's symmetry of
  `b` is not needed), which implies B's literal one (`f` not identically zero on `O`), the
  open-set/support clauses being repackaged as `U = O ∩ W`.  `admitsBumpFunctions_of_hilbert`
  gives `AdmitsBumpFunctions` (pointwise), hence `AdmitsBumpFunctionsWeak`; its hypothesis (a chart
  of the structure around every point with Hilbert `E₀`) comes from B's equivalent atlas of
  sc-Hilbert charts (only level `0` is used).
* `B → A`: NOT proved, for genuine reasons.  (1) A's conclusions are the pointwise notions
  (`HasBumpProperty`, `AdmitsBumpFunctions`, `f(x) ≠ 0`), B gives only the literal ones (`f` not
  identically zero), and on retracts the weak notion does not yield the pointwise one by glue (no
  translations).  (2) `hasBumpProperty_of_quadratic` assumes only `κ‖v‖² ≤ b(v, v)` for a continuous
  bilinear `b` (a Hilbertable `E₀`, `b` not even symmetric), more than B's "the norm of `E₀` is
  Hilbert"; B cannot be applied to a renormed space without rebuilding the local model.
-/

namespace RoundTrip.V5_53
open Polyfold Set Function

/-- The project's statement, universe `0` for `admitsBumpFunctions_of_hilbert`. -/
def A : Prop :=
  (type_of% @Polyfold.LocalModel.hasBumpProperty_of_quadratic) ∧
  (type_of% @Polyfold.proposition_5_35) ∧
  (type_of% @Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert.{0})

theorem A_holds : A :=
  ⟨@Polyfold.LocalModel.hasBumpProperty_of_quadratic, @Polyfold.proposition_5_35,
    @Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert.{0}⟩

/-- The project's (pointwise) bump property implies B's literal one. -/
theorem hasBumpPropertyB_of_hasBumpProperty {M : LocalModel} (h : M.HasBumpProperty) :
    HasBumpPropertyB M := by
  rintro x hx _ - hxU ⟨W, hW, rfl⟩ hcl
  obtain ⟨f, hf, hfx, hsupp⟩ := h x hx W hW hxU.2 hcl
  exact ⟨f, hf, ⟨x, hx, hfx⟩, fun z hz => ⟨hz.2, hsupp hz⟩⟩

theorem A_to_B : A → B := by
  rintro ⟨-, h535, hhilb⟩
  refine ⟨fun M ⟨b, _, hb⟩ => hasBumpPropertyB_of_hasBumpProperty
    (h535 M ⟨b, fun v => (hb v).symm⟩), ?_⟩
  rintro X _ _ _ PX ⟨At, hAt, hH⟩
  refine MPolyfold.AdmitsBumpFunctions.weak (@hhilb X _ _ _ PX fun x => ?_)
  obtain ⟨φ, hφ, hxφ⟩ := At.cover x
  obtain ⟨b, -, hb⟩ := hH φ hφ 0
  exact ⟨φ, fun ψ hψ => (MAtlas.equiv_iff _ _).1 hAt φ hφ ψ hψ, hxφ, b, fun v => (hb v).symm⟩

#rt_check RoundTrip.V5_53.A_to_B [Polyfold.LocalModel.hasBumpProperty_of_quadratic,
  Polyfold.proposition_5_35, Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert]

end RoundTrip.V5_53
