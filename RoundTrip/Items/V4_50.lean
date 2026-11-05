import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_50

/-!
Round trip for V4_50 (Theorem 4.22).  `A` is the type of `Polyfold.MPolyfold.theorem_4_22`
(universe `0`).

Neither direction is proved; the parts of B that `A` does give are proved as `A_to_B23`
(statements (2) and (3) of the theorem, on `A`'s neighbourhood `U`).

* (1) and (4) differ in content.  `A` (1) counts the faces of the **model retract `O`** of a tame
  chart `ψ` centred at `x` that pass through `ψ(x) = 0` (Corollary 2.41 in the chart: `d_X(x)` of
  them); `A` (4) describes `F_σ` as `ψ⁻¹(G ∩ ⋂_{i∈σ} F_i)` with `F_i` faces of `O` through `0`
  (`R.IsRetractFace`, inside the coordinate hyperplanes) and an open `G` depending on `σ`, and adds
  `d_{F_σ} + #σ = d_X`.  B (1) asks for one open `U ∋ x` whose **own faces** (closures in `U` of
  connected components of `U ∩ {d_X = 1}`) are exactly `d_X(x)` sets, all through `x`, and B (4)
  uses `F_σ = U ∩ ⋂_{i∈σ} F_i` for these faces of `U`.  Going from `A` to B needs a local face
  structure theorem for small neighbourhoods in `X` (connectedness of `U ∩ {d = 1}` near each
  coordinate hyperplane, every face of `U` reaching `x`, and the identification of the faces of
  `U` with `ψ⁻¹` of the retract faces of `O`, plus restriction of (4) from `ψ⁻¹(G ∩ ⋂ F_i)` to
  `U ∩ ⋂ F_i`), which `A` does not contain.
* Conversely B gives no chart (`ψ`, the tame retraction `R`, the presentation `T`, `U ⊆ dom ψ`),
  no coordinate description of the local faces and not `d_{F_σ} + #σ = d_X`, all part of `A`.
-/

namespace RoundTrip.V4_50
open Polyfold

def A : Prop := type_of% @Polyfold.MPolyfold.theorem_4_22.{0}

theorem A_holds : A := @Polyfold.MPolyfold.theorem_4_22.{0}

/-- Statements (2) and (3) of B (on a common open `U ∋ x`). -/
def B23 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X) (x : X),
    P.IsTame → P.IsSmoothSubmanifold A → x ∈ A → P.IsGeneralPositionAt A x →
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      (∃ (hA : P.IsSubMPolyfold A) (_ : ParacompactSpace A),
        ∀ a : A, a.1 ∈ U → P.degIndex a.1 = (P.subPolyfold hA).degIndex a) ∧
      (∀ a ∈ A ∩ U, P.IsGeneralPositionAt A a)

/-- `A` gives (2) and (3) of B. -/
theorem A_to_B23 : A → B23 := by
  intro hA X _ _ _ P S x hP hS _ hgp
  have : ParacompactSpace S := P.paracompactSpace_subtype S
  obtain ⟨ψ, -, hx, -, R, n, Wq, T, -, -, -, U, hU, hxU, -, -, -, h2, h3, -⟩ := hA hP hS hgp
  exact ⟨U, hU, hxU, ⟨hS.isSubMPolyfold, this, fun a ha => (h2 a ha).symm⟩,
    fun a ha => h3 a ⟨ha.2, ha.1⟩⟩

#rt_check RoundTrip.V4_50.A_to_B23 [Polyfold.MPolyfold.theorem_4_22]

end RoundTrip.V4_50
