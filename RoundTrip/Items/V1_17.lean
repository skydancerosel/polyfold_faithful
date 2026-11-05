import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_17

/-! Round trip for V1_17 (Proposition 1.18: sc^k maps are `C^k` from `U_{m+k}` to `F_m`).

`A` is the conjunction of the types of `Polyfold.IsSck.contDiffOn_levels'`,
`Polyfold.IsSck.contDiffOn_levels`, `Polyfold.IsSck.contDiffOn_levels_of_le`,
`Polyfold.IsSck.contDiffOn_base` and `Polyfold.IsScSmooth.contDiffOn_levels`.  None has universe
parameters (`ScBanach` lives in `Type`).

`A → B`: relatively open subsets of partial quadrants are `IsScDomain`s
(`IsRelOpenInQuadrant.isScDomain`), and the blind level map `levelTo f (m+l) m` is the project's
`levelMap f m ∘ E.inclK m l` (both are `invFun ι_m ∘ f ∘ ι_{m+l}`).

`B → A` fails: every statement of `A` is for an arbitrary `IsScDomain` `U` (on every level open ∩
convex with unique differentiability), a strictly larger class of domains than the relatively open
subsets of partial quadrants of `B`.  Restricted to the latter, the most general conjunct of `A`
(`contDiffOn_levels'`, with an arbitrary compatible level-lowering operator `ρ`) does follow from
`B`: see `B_to_levels'_quadrant`. -/

namespace RoundTrip.V1_17
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsSck.contDiffOn_levels') ∧ (type_of% @Polyfold.IsSck.contDiffOn_levels) ∧
    (type_of% @Polyfold.IsSck.contDiffOn_levels_of_le) ∧ (type_of% @Polyfold.IsSck.contDiffOn_base) ∧
    (type_of% @Polyfold.IsScSmooth.contDiffOn_levels)

theorem A_holds : A :=
  ⟨@Polyfold.IsSck.contDiffOn_levels', @Polyfold.IsSck.contDiffOn_levels,
    @Polyfold.IsSck.contDiffOn_levels_of_le, @Polyfold.IsSck.contDiffOn_base,
    @Polyfold.IsScSmooth.contDiffOn_levels⟩

/-- The blind level map is the project's level map composed with the inclusion. -/
theorem levelTo_eq {E F : ScBanach} (f : E.lvl 0 → F.lvl 0) (m l : ℕ) :
    levelTo f (m + l) m = levelMap f m ∘ E.inclK m l := by
  funext x
  simp only [levelTo, levelMap, Function.comp, E.toBase_inclK]

/-- More generally, for any compatible `ρ : E_n → E_m`. -/
theorem levelTo_eq' {E F : ScBanach} (f : E.lvl 0 → F.lvl 0) {m n : ℕ} (ρ : E.lvl n →L[ℝ] E.lvl m)
    (hρ : ∀ x, E.toBase m (ρ x) = E.toBase n x) : levelTo f n m = levelMap f m ∘ ρ := by
  funext x
  simp only [levelTo, levelMap, Function.comp, hρ]

theorem A_to_B : A → B := by
  intro hA E F C U C' V f k hU _ hfV hf
  have hD := hU.isScDomain
  refine ⟨fun m => ⟨?_, ?_⟩, fun m l hl => ?_⟩
  · rw [levelTo_eq]
    intro x hx
    have hx' : E.inclK m k x ∈ E.lvlSet U m := by
      rw [ScBanach.mem_lvlSet, E.toBase_inclK]; exact hx
    exact hf.isSc0.levelMap_mapsTo hfV m hx'
  · rw [levelTo_eq]
    exact hA.2.1 hD hf m
  · rw [levelTo_eq]
    exact hA.2.2.1 hl hD hf m

/-- What `B` does give: `A`'s most general conjunct `contDiffOn_levels'`, restricted to relatively
open subsets of partial quadrants (instead of arbitrary `IsScDomain`s). -/
theorem B_to_levels'_quadrant (hB : B) : ∀ {k : ℕ} {E F : ScBanach} {C U : Set (E.lvl 0)}
    {f : E.lvl 0 → F.lvl 0}, IsRelOpenInQuadrant E C U → IsSck k E F U f → ∀ {m n : ℕ},
    n = m + k → ∀ (ρ : E.lvl n →L[ℝ] E.lvl m), (∀ x, E.toBase m (ρ x) = E.toBase n x) →
    ContDiffOn ℝ k (levelMap f m ∘ ρ) (E.lvlSet U n) := by
  intro k E F C U f hU hf m n hn ρ hρ
  subst hn
  have hV : IsRelOpenInQuadrant F Set.univ Set.univ :=
    ⟨isPartialQuadrant_univ F, Set.univ, isOpen_univ, (Set.univ_inter _).symm⟩
  have h := ((hB E F C U Set.univ Set.univ f k hU hV (Set.mapsTo_univ _ _) hf).1 m).2
  rwa [levelTo_eq' f ρ hρ] at h

#rt_check RoundTrip.V1_17.A_to_B [Polyfold.IsSck.contDiffOn_levels', Polyfold.IsSck.contDiffOn_levels,
  Polyfold.IsSck.contDiffOn_levels_of_le, Polyfold.IsSck.contDiffOn_base,
  Polyfold.IsScSmooth.contDiffOn_levels]
#rt_check RoundTrip.V1_17.B_to_levels'_quadrant [Polyfold.IsSck.contDiffOn_levels',
  Polyfold.IsSck.contDiffOn_levels, Polyfold.IsSck.contDiffOn_levels_of_le,
  Polyfold.IsSck.contDiffOn_base, Polyfold.IsScSmooth.contDiffOn_levels]

end RoundTrip.V1_17
