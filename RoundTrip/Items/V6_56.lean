import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_56

/-! Round trip for V6_56 (transport along paths from local push-forwards; the proof of Thm 6.37).

A is the conjunction of the 19 theorems of the row: the ABSTRACT transport theory of
`LocalTransport PX O` (any family of types `O x` over the smooth points, any good open sets
covering `X_∞`, any push-forwards along paths in good sets which compose and do not depend on the
good set): dyadic transport, its stabilization, Lebesgue numbers, (∗) `transport_eq_push`,
homotopy invariance (`transport_eq_of_isScHomotopyRel`, via the square lemma `transportN_square`),
reparametrization, the concatenation rule and the uniqueness `transport_unique`, plus the pasting
lemma `equiv_paste_squares` (universes at `0`; `equiv_paste_squares` is stated for `Sort*` and is
instantiated at `Sort 1 = Type`, since `Sort 0` would make it a statement about `Prop`).

B is CONCRETE: for every tame `X` and sc-Fredholm `f` (no bump functions, no tame germ data, no
sc⁺-sections), (a) every point `γ(t₀)` of an sc-smooth path has an ORIENTABLE neighbourhood
(open, sc-smoothly contractible, with the local propagation property) containing `γ(I ∩ [0, 1])`
for an open interval `I ∋ t₀`; (b) the chain transport `ChainB` from `0` to `1` is a well-defined
map `o₀ ↦ o₁`; (c) it depends only on the homotopy class; (d) the functor of Theorem 6.37 with B's
property (∗) is unique.

Neither direction is proved; the two statements are about different objects.
* `A → B`: A says nothing about orientations, `HasLocalPropagation` or contractibility.  It would
  have to be instantiated with the project's `orLocalTransport` (V6_57), which needs bump functions,
  a tame section and sc⁺-sections (not in B), and B's (a) asserts, for every tame `X` and every
  sc-Fredholm `f`, that every smooth point has an open sc-smoothly contractible neighbourhood with
  the local propagation property (`B_implies_orNbhdCover` below): the project proves open
  neighbourhoods with the local propagation property only under bump functions and a tame section
  (Theorem 6.35), and never contractible ones.  The chain relation `ChainB` (pushes in contractible
  orientable neighbourhoods, along arbitrary subdivisions) is not the project's dyadic transport
  either; relating them would be glue, but it rests on the same missing neighbourhoods.  B's (d) is
  V6_57's uniqueness, which needs the same cover (V6_57 `A_to_BExtra`).
* `B → A`: B is about one instance; A's theorems hold for every `LocalTransport` and cannot follow.
-/

namespace RoundTrip.V6_56
open Polyfold Set

/-- The project's statement (the 19 theorems of the row), universes instantiated at `0`
(`equiv_paste_squares` at `Sort 1`). -/
def A : Prop :=
  type_of% @Polyfold.LocalTransport.push_eq_refl.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.push_eq_push.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.push_congr.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.transportN_eq_push.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.transportN_eq_of_isFine.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.exists_isLebesgueNumber.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.isFine_of_isLebesgueNumber.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.transport_eq_push.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.transport_congr.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.transport_const.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.transport_halves.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.transportN_square.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.exists_isSqLebesgueNumber.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.transport_eq_of_isScHomotopyRel.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.transport_reparam.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.transport_concatPath.{0, 0} ∧
  type_of% @Polyfold.LocalTransport.transport_unique.{0, 0} ∧
  type_of% @Polyfold.equiv_paste_squares.{1, 1, 1, 1, 1, 1, 1, 1, 1}

theorem A_holds : A :=
  ⟨@Polyfold.LocalTransport.push_eq_refl.{0, 0}, @Polyfold.LocalTransport.push_eq_push.{0, 0},
    @Polyfold.LocalTransport.push_congr.{0, 0}, @Polyfold.LocalTransport.transportN_eq_push.{0, 0},
    @Polyfold.LocalTransport.transportN_eq_of_isFine.{0, 0},
    @Polyfold.LocalTransport.exists_isLebesgueNumber.{0, 0},
    @Polyfold.LocalTransport.isFine_of_isLebesgueNumber.{0, 0},
    @Polyfold.LocalTransport.transport_eq_push.{0, 0},
    @Polyfold.LocalTransport.transport_congr.{0, 0},
    @Polyfold.LocalTransport.transport_const.{0, 0},
    @Polyfold.LocalTransport.transport_halves.{0, 0},
    @Polyfold.LocalTransport.transportN_square.{0, 0},
    @Polyfold.LocalTransport.exists_isSqLebesgueNumber.{0, 0},
    @Polyfold.LocalTransport.transport_eq_of_isScHomotopyRel.{0, 0},
    @Polyfold.LocalTransport.transport_reparam.{0, 0},
    @Polyfold.LocalTransport.transport_concatPath.{0, 0},
    @Polyfold.LocalTransport.transport_unique.{0, 0},
    @Polyfold.equiv_paste_squares.{1, 1, 1, 1, 1, 1, 1, 1, 1}⟩

/-- **What B's (a) asserts**: for every tame `X` and every sc-Fredholm `f`, every smooth point has an
orientable neighbourhood in B's sense (open, sc-smoothly contractible, with the local propagation
property in some chart). -/
def OrNbhdCover : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
    PX.IsTame → ∀ x ∈ PX.smoothSet, ∃ (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (U : Set X),
      IsOrNbhdB f hf c hc U x

/-- B's (a) for the constant path at `x` (and `t₀ = 0`). -/
theorem B_implies_orNbhdCover : B → OrNbhdCover := by
  intro hB X _ _ _ PX Y _ _ _ P _ _ _ _ Bd f hf hX x hx
  obtain ⟨c, hc, U, hN, -⟩ := (hB PX P Bd f hf hX).1 (fun _ => x)
    (isScSmoothMap_const_of_mem_smoothSet hx) 0 ⟨le_rfl, zero_le_one⟩
  exact ⟨c, hc, U, hN⟩

#rt_check RoundTrip.V6_56.B_implies_orNbhdCover [Polyfold.LocalTransport.push_eq_refl,
  Polyfold.LocalTransport.push_eq_push, Polyfold.LocalTransport.push_congr,
  Polyfold.LocalTransport.transportN_eq_push, Polyfold.LocalTransport.transportN_eq_of_isFine,
  Polyfold.LocalTransport.exists_isLebesgueNumber, Polyfold.LocalTransport.isFine_of_isLebesgueNumber,
  Polyfold.LocalTransport.transport_eq_push, Polyfold.LocalTransport.transport_congr,
  Polyfold.LocalTransport.transport_const, Polyfold.LocalTransport.transport_halves,
  Polyfold.LocalTransport.transportN_square, Polyfold.LocalTransport.exists_isSqLebesgueNumber,
  Polyfold.LocalTransport.transport_eq_of_isScHomotopyRel, Polyfold.LocalTransport.transport_reparam,
  Polyfold.LocalTransport.transport_concatPath, Polyfold.LocalTransport.transport_unique,
  Polyfold.equiv_paste_squares]

end RoundTrip.V6_56
