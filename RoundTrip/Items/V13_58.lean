import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V13_58

set_option maxSynthPendingDepth 3

/-! Round trip for V13_58 (2021 Theorem 13.5.7, p. 635; 2017: Theorem 13.10: a structurable
sc⁺-multisection is a locally finite commensurable sum of atomic ones).

The item lists the definition `CommData.smulFunOver` (vocabulary) and four theorems; `A` is the
conjunction of their types at universe `0` (`B` is on `SEP.{0}`).

**Neither direction is proved.**

* `A ⇒ B`: `A` gives the summands `Λⱼ` as `IsAtomicOn` (Definition 13.5.1 with `U(xⱼ)` a
  `NatNbhd`: an open invariant subset of the domain of a natural representation, as the good
  system provides it; not required to be connected, and the properness property is asked of
  `cl U(xⱼ)` only).  `B` asks `IsAtomic` (Definition 13.5.1 with `U(x)` the connected domain of a
  natural representation with the properness property).  `IsAtomic ⇒ IsAtomicOn` holds
  (`IsAtomic.isAtomicOn`); the converse does not hold for the notions as defined: if `U(x)` has
  several components, the points of the other components are not reachable from the component of
  `x` (every morphism between points of the representation domain is some `Γ(g, ·)`, and `Φ(g)`
  fixes the component of `x`), so an `IsAtomicOn` functor charging them is not related to data on
  a connected domain.  `B` is believed to hold, but its proof would rerun the construction with
  `V(xⱼ)` inside a connected invariant neighbourhood with proper closure (local connectedness of
  the object M-polyfold, small natural representations), not glue.
  Everything else in `B` comes from `A` by glue: `c := ofTuple T`, `o := Over.ofTuple T`
  (after `T.Λ = Λ`), `J := X`, and the class equation is `theorem_13_5_7_book`'s.
* `B ⇒ A`: the main conjunct `theorem_13_5_7` is a statement about **every** structured tuple
  `T = (Λ, 𝒰, S, τ)`: the decomposition over `T`'s own data `ofTuple T`, keeping the sections
  `sˣᵢ` of `T` on every `U(x)`.  `B` only gives some common data `c` and some structure `o` over it.
  Also `A` indexes the family by `X` (`J = X`, the points `xⱼ`), `B` by an arbitrary `J : Type`;
  reindexing a `J`-family by `X` is not a renaming (several summands may share a point, and `X`
  may be finite while `J` is larger).  The weaker `theorem_13_5_7_book` would follow from `B`
  (`T := o.toTuple`, `ofTuple o.toTuple` is `c` by eta, `IsAtomic.isAtomicOn`) except for this
  indexing.
-/

namespace RoundTrip.V13_58
open Polyfold Polyfold.SBLocalization

/-- The project's statement at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.multisectionSmulFun_of_eq_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_orbit_nbhd.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_5_7.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_5_7_book.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.multisectionSmulFun_of_eq_zero.{0},
    @Polyfold.SBLocalization.exists_orbit_nbhd.{0},
    @Polyfold.SBLocalization.theorem_13_5_7.{0},
    @Polyfold.SBLocalization.theorem_13_5_7_book.{0}⟩

/-- The glue of `A ⇒ B` apart from atomicity: `A`'s decomposition gives every clause of `B`
with `IsAtomicOn` in place of `IsAtomic`. -/
theorem A_to_B_on (hA : A) :
    ∀ A : SEP.{0}, A.X.HasParacompactOrbitSpace → A.X.HasScPartitionsOfUnity →
    ∀ Λ : A.W → ℚ≥0, IsStructurable A Λ →
      ∃ (c : CommData A) (o : c.Over Λ) (J : Type) (Λj : J → A.W → ℚ≥0)
        (oj : ∀ j, c.Over (Λj j)) (hlf : IsLocallyFiniteFamily Λj),
        (∀ j, SBLocalization.IsAtomicOn A (Λj j)) ∧
        CommData.lfSum oj hlf = Λ ∧
        (CommData.Over.lfSum oj hlf).toStructured = o.toStructured := by
  intro A hpara hpu Λ hΛ
  obtain ⟨T, Λf, o, hlf, hT, hat, hsum, hcl⟩ := hA.2.2.2 hpara hpu hΛ
  subst hT
  exact ⟨_, CommData.Over.ofTuple T, A.Obj, Λf, o, hlf, hat, hsum, hcl⟩

/-- `IsAtomic` is the stronger notion (the converse is what `A ⇒ B` would need). -/
example {A : SEP.{0}} {Λ : A.W → ℚ≥0} (h : SBLocalization.IsAtomic A Λ) :
    SBLocalization.IsAtomicOn A Λ :=
  h.isAtomicOn

#rt_check RoundTrip.V13_58.A_to_B_on [Polyfold.SBLocalization.multisectionSmulFun_of_eq_zero,
  Polyfold.SBLocalization.exists_orbit_nbhd, Polyfold.SBLocalization.theorem_13_5_7,
  Polyfold.SBLocalization.theorem_13_5_7_book]

end RoundTrip.V13_58
