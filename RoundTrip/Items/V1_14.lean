import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_14

/-! Round trip for V1_14 (Definition 1.15: sc^k and sc-smooth maps; "then `T²f` is sc⁰").

`A` is the conjunction of the types of the theorems in the item's declaration list:
`IsSck.of_succ`, `IsSck.of_le`, `isScSmooth_iff`, `IsSck.congr` (the definitions `IsSck`,
`IsScSmooth` are vocabulary).  None has universe parameters (`ScBanach` lives in `Type`).

Blind vs project notions: `tanSet E U = E.tangentSet U`, `tanMap f D = tangentMapWith f D` (both
`rfl`), `Sc1With U f D ↔ IsSc1With U f D` (same three fields).  The blind `SckB (k+1)` asks for
SOME derivative family `D` with `Tf = tanMap f D` sc^k, the project's `IsSck (k+1)` uses the
CHOSEN family `scDeriv U f`; on `IsScDomain`s (in particular on relatively open subsets of partial
quadrants) the two agree (`sckB_iff_isSck`, proved outright), since `Df(x)` is unique on `U₁`.

`A → B` goes through the project's `IsSck`, using `A`'s `IsSck.congr` (choice-independence) for
`SckB 2 → IsSck 2` and again to pass from the chosen derivatives to arbitrary ones.
`B → A` is vacuous: `A`'s conjuncts are structural facts for arbitrary `U` (or arbitrary
`IsScDomain`s), which `B` (a property of `sc²` maps on tuples) cannot supply; they are re-proved
outright. -/

namespace RoundTrip.V1_14
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsSck.of_succ) ∧ (type_of% @Polyfold.IsSck.of_le) ∧
    (type_of% @Polyfold.isScSmooth_iff) ∧ (type_of% @Polyfold.IsSck.congr)

theorem A_holds : A :=
  ⟨@Polyfold.IsSck.of_succ, @Polyfold.IsSck.of_le, @Polyfold.isScSmooth_iff,
    @Polyfold.IsSck.congr⟩

/-! ### The blind notions are the project's -/

theorem tanSet_eq (E : ScBanach) (U : Set (E.lvl 0)) : tanSet E U = E.tangentSet U := rfl

theorem tanMap_eq {E F : ScBanach} (f : E.lvl 0 → F.lvl 0) (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0) :
    tanMap f D = tangentMapWith f D := rfl

theorem sc1With_iff {E F : ScBanach} (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0) : Sc1With U f D ↔ IsSc1With U f D :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.isSc0, h.hasFDerivWithinAt, h.tangent_isSc0⟩⟩

/-- `IsSck.congr`, re-proved outright (to be used where `A` may not be). -/
theorem isSck_congr' : ∀ {k : ℕ} {E F : ScBanach} {U : Set (E.lvl 0)} {f f' : E.lvl 0 → F.lvl 0},
    IsScDomain E U → EqOn f f' U → IsSck k E F U f → IsSck k E F U f'
  | 0, _, _, _, _, _, _, hff', h => IsSc0.congr h hff'
  | k + 1, _, _, _, _, _, hU, hff', h =>
    ⟨h.1.congr hff', isSck_congr' (k := k) hU.tangentSet (h.1.tangentMap_congr hU hff') h.2⟩

/-- `SckB k → IsSck k` on `IsScDomain`s, given a congruence principle for `IsSck`. -/
theorem isSck_of_sckB (hcongr : type_of% @Polyfold.IsSck.congr) :
    ∀ (k : ℕ) {E F : ScBanach} {U : Set (E.lvl 0)} {f : E.lvl 0 → F.lvl 0},
      IsScDomain E U → SckB k E F U f → IsSck k E F U f
  | 0, _, _, _, _, _, h => h
  | k + 1, _, _, _, _, hU, ⟨D, h1, h2⟩ => by
    have h1' := (sc1With_iff _ _ _).1 h1
    refine ⟨h1'.isSc1, ?_⟩
    have := isSck_of_sckB hcongr k hU.tangentSet h2
    exact hcongr hU.tangentSet (IsSc1.tangentMap_eqOn h1' (hU.uniqueDiffWithinAt 1)).symm this

/-- `IsSck k → SckB k` (any `U`): take the chosen derivative families. -/
theorem sckB_of_isSck : ∀ (k : ℕ) {E F : ScBanach} {U : Set (E.lvl 0)} {f : E.lvl 0 → F.lvl 0},
    IsSck k E F U f → SckB k E F U f
  | 0, _, _, _, _, h => h
  | k + 1, _, _, _, _, h =>
    ⟨_, (sc1With_iff _ _ _).2 h.1.isSc1With_scDeriv, sckB_of_isSck k h.2⟩

/-- The blind `SckB` is the project's `IsSck` on `IsScDomain`s (hence on tuples). -/
theorem sckB_iff_isSck (k : ℕ) {E F : ScBanach} {U : Set (E.lvl 0)} {f : E.lvl 0 → F.lvl 0}
    (hU : IsScDomain E U) : SckB k E F U f ↔ IsSck k E F U f :=
  ⟨isSck_of_sckB @isSck_congr' k hU, sckB_of_isSck k⟩

theorem ScSmoothB_iff {E F : ScBanach} {U : Set (E.lvl 0)} {f : E.lvl 0 → F.lvl 0}
    (hU : IsScDomain E U) : ScSmoothB (F := F) U f ↔ IsScSmooth U f :=
  forall_congr' fun k => sckB_iff_isSck k hU

/-! ### The round trip -/

theorem A_to_B : A → B := by
  intro hA E F C U C' V f hU _ _ hf D D' hD hD'
  have hUd := hU.isScDomain
  have hTUd := hUd.tangentSet
  -- `f` is sc² in the project's sense (uses `A`'s `IsSck.congr`)
  have h2 : IsSck 2 E F U f := isSck_of_sckB hA.2.2.2 2 hUd hf
  have hD1 := (sc1With_iff _ _ _).1 hD
  -- `Tf` with the given `D` is sc¹ (`A`'s `IsSck.congr` again)
  have hT : IsSck 1 E.tangent F.tangent (E.tangentSet U) (tangentMapWith f D) :=
    hA.2.2.2 hTUd (IsSc1.tangentMap_eqOn hD1 (hUd.uniqueDiffWithinAt 1)) h2.2
  -- its tangent map with the given `D'` is the chosen one on `T(TU)`
  have hD1' : IsSc1With (E.tangentSet U) (tangentMapWith f D) D' := (sc1With_iff _ _ _).1 hD'
  exact IsSc0.congr hT.2 (IsSc1.tangentMap_eqOn hD1' (hTUd.uniqueDiffWithinAt 1))

/-! ### `B → A` (vacuous): the conjuncts of `A`, re-proved outright -/

theorem of_succ' : ∀ {k : ℕ} {E F : ScBanach} {U : Set (E.lvl 0)} {f : E.lvl 0 → F.lvl 0},
    IsSck (k + 1) E F U f → IsSck k E F U f
  | 0, _, _, _, _, h => h.1.isSc0
  | k + 1, _, _, _, _, h => ⟨h.1, of_succ' (k := k) h.2⟩

theorem B_to_A : B → A := by
  intro _
  refine ⟨@of_succ', ?_, ?_, @isSck_congr'⟩
  · intro E F k l hkl U f h
    induction hkl with
    | refl => exact h
    | step _ ih => exact ih (of_succ' h)
  · intro E F U f
    exact ⟨fun h => ⟨(h 1).1, fun k => (h (k + 1)).2⟩, fun h k => by
      cases k with
      | zero => exact h.1.isSc0
      | succ k => exact ⟨h.1, h.2 k⟩⟩

#rt_check RoundTrip.V1_14.A_to_B [Polyfold.IsSck.of_succ, Polyfold.IsSck.of_le,
  Polyfold.isScSmooth_iff, Polyfold.IsSck.congr]
#rt_check RoundTrip.V1_14.B_to_A [Polyfold.IsSck.of_succ, Polyfold.IsSck.of_le,
  Polyfold.isScSmooth_iff, Polyfold.IsSck.congr]
#rt_check RoundTrip.V1_14.sckB_iff_isSck [Polyfold.IsSck.of_succ, Polyfold.IsSck.of_le,
  Polyfold.isScSmooth_iff, Polyfold.IsSck.congr]
#rt_overlap RoundTrip.V1_14.B_to_A [Polyfold.IsSck.of_succ, Polyfold.IsSck.of_le,
  Polyfold.isScSmooth_iff, Polyfold.IsSck.congr]

end RoundTrip.V1_14
