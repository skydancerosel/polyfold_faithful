import Polyfold
/-! Blind formalization of V2_49 (the text's §2.4, Proposition 2.43, pp. 44–45).

Text: for a tame retraction `r` onto `O` and a face `F` of `O`: there are an open neighbourhood
`V*` of `F` in `U` and an sc-smooth retraction `s : V* → V*` onto `F`; `s` restricted to
`V = O ∩ V*` makes `F` a sub-M-polyfold of `O`.  `F` is tame and `d_F(x) = d_O(x) − 1` for
`x ∈ F`.

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C ⊆ E₀`, a tame sc-smooth
  retraction `R : ScRetraction E C` (Definition 2.1 with Definition 2.34: the project's
  `ScRetraction`, checked with `#print`: `r : U → U` sc-smooth, `r ∘ r = r` on `U`, `U` relatively
  open in the partial quadrant `C`; and `R.IsTame`, checked: for every presentation `T` of `C`,
  `d_C ∘ r = d_C` on `U` and an sc-complement of `Dr(x)E` inside `E_x` at smooth `x ∈ O`),
  `O = R.retract = r(U)`, assumed nonempty (a face is nonempty, and the M-polyfold `O` needs a
  point).
- `O` as an M-polyfold, faces, `d_O`: as in my `RoundTrip/Blind/V2_46.lean`: the project's
  `LocalModel.toMPolyfold` (the subtype `↥O` with the single chart `id`), `MPolyfold.IsFace`
  (Definition 2.39) and `MPolyfold.degIndex` (Definition 2.22).  `F` is a subset of `↥O`; its image
  in `E₀` is `Subtype.val '' F`.
- "Open neighbourhood `V*` of `F` in `U`, sc-smooth retraction `s : V* → V*` onto `F`": an
  `ScRetraction E C` `s` with `s.U ⊆ U`, `F ⊆ s.U` and `s.retract = s(V*) = F`.  (`V*` open in `U`
  is the same as: relatively open in `C` and contained in `U`, since `U` is relatively open in
  `C`.)
- "`s` restricted to `V = O ∩ V*` makes `F` a sub-M-polyfold of `O`": with `V = {y ∈ O | y ∈ V*}`
  (open in `O`) and `s|_V : V → V` seen as a map of the M-polyfold `O` (`restrictB`, a total map
  `↥O → ↥O`, equal to `s` where `s` lands in `O` and the identity elsewhere — on `V` it is `s`),
  B asserts the data of Definition 2.20 with this single `V`: `s|_V` is sc-smooth on `V` in the
  M-polyfold `O` (the project's `MPolyfold.IsScSmoothOn`, Definition 2.14, checked: continuous on
  `V` and sc-smooth in all pairs of charts), maps `V` into `V`, is idempotent on `V`, and
  `s|_V(V) = F ∩ V`.
- "`F` is tame", `d_F`: `F` with its induced structure as a sub-M-polyfold of `O`, the project's
  `subPolyfold` (Proposition 2.21, checked: the sub-charts `φ|_{W ∩ F}`); it needs `↥F` paracompact
  as an instance, which B asserts together with the sub-M-polyfold property (as in
  `RoundTrip/Blind/V2_51.lean`; true, `F` is closed in a metrizable space).  Tame is
  `MPolyfold.IsTame` (Definition 2.37, checked: an equivalent atlas of charts modelled on tame
  retracts — a property of the given structure).
- `d_F(x) = d_O(x) − 1` is written `d_F(x) + 1 = d_O(x)` in `ℕ` (the integer reading; it does not
  hide a truncated subtraction), for every `x ∈ F`.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_49
open Polyfold

open Classical in
/-- The restriction `s|_V` of a map `s : E₀ → E₀` to `V = O ∩ V*`, as a map `↥O → ↥O`: `s(y)` when
it lies in `O` (always the case on `V`), and `y` otherwise. -/
noncomputable def restrictB {E : ScBanach} (O : Set (E.lvl 0)) (s : E.lvl 0 → E.lvl 0) (y : O) :
    O :=
  if h : s y.1 ∈ O then ⟨s y.1, h⟩ else y

/-- Proposition 2.43: a face `F` of a tame retract `O = r(U)` is the image of an sc-smooth
retraction `s : V* → V*` of an open neighbourhood `V* ⊆ U` of `F`; `s|_{O ∩ V*}` exhibits `F` as a
sub-M-polyfold of `O`; `F` is tame with `d_F = d_O − 1`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (R : ScRetraction E C) (hne : R.retract.Nonempty),
    R.IsTame →
      ∀ F : Set R.retract,
        ((LocalModel.mk E C R.retract ⟨R, rfl⟩).toMPolyfold hne).IsFace F →
          -- `s : V* → V*` onto `F`, `V*` an open neighbourhood of `F` in `U`
          (∃ s : ScRetraction E C, s.U ⊆ R.U ∧ Subtype.val '' F ⊆ s.U ∧
            s.retract = Subtype.val '' F ∧
            -- `s|_V`, `V = O ∩ V*`, exhibits `F` as a sub-M-polyfold of `O`
            ((LocalModel.mk E C R.retract ⟨R, rfl⟩).toMPolyfold hne).IsScSmoothOn
                ((LocalModel.mk E C R.retract ⟨R, rfl⟩).toMPolyfold hne)
                (restrictB R.retract s.toFun) {y | y.1 ∈ s.U} ∧
            Set.MapsTo (restrictB R.retract s.toFun) {y | y.1 ∈ s.U} {y | y.1 ∈ s.U} ∧
            (∀ y ∈ {y : R.retract | y.1 ∈ s.U},
              restrictB R.retract s.toFun (restrictB R.retract s.toFun y) =
                restrictB R.retract s.toFun y) ∧
            restrictB R.retract s.toFun '' {y | y.1 ∈ s.U} = F ∩ {y | y.1 ∈ s.U}) ∧
          -- `F` is a tame sub-M-polyfold with `d_F = d_O − 1`
          (∃ (hF : ((LocalModel.mk E C R.retract ⟨R, rfl⟩).toMPolyfold hne).IsSubMPolyfold F)
            (_ : ParacompactSpace F),
            (((LocalModel.mk E C R.retract ⟨R, rfl⟩).toMPolyfold hne).subPolyfold hF).IsTame ∧
            ∀ x : F,
              (((LocalModel.mk E C R.retract ⟨R, rfl⟩).toMPolyfold hne).subPolyfold hF).degIndex x
                  + 1 =
                ((LocalModel.mk E C R.retract ⟨R, rfl⟩).toMPolyfold hne).degIndex x)

end RoundTrip.V2_49
