import Polyfold
/-! Blind formalization of V10_60 (the text's Part II, §10.5, Remark 10.5.5, p. 508 of the
Springer 2021 book; new in the 2021 edition).

Text: for `[D], [D'] : P → P'` with `|𝒟| = |𝒟'|` it is in general not true that `[D] = [D']`,
but `[D]_* = [D']_*` and `[D]^* = [D']^*`.

Choices:
- Setting: universe 0; the project's `SEP.{0}`, `GenSBMap`, `GenSBMap.IsGeneralizedIso`
  (V10_51, V10_56).  `[D]`, `[D']` are generalized strong bundle isomorphisms (the push-forwards
  are defined only for these; the remark follows Theorem 10.5.4), in both parts.
- `|𝒟|` is the square of orbit maps of (10.24) (V10_53): the pair of `|[D]| : |W| → |W'|` (the
  project's `GenSBMap.orbitMap`, V10_52) and `|[d]| : |X| → |X'|` (the project's `EPLoc.orbitMap`
  of `GenSBMap.base [D]`, the generalized map of the bases covered by `[D]`, V10_52).
  `|𝒟| = |𝒟'|`: both maps agree.
- "in general not true": the negation of the universal statement, i.e. some generalized strong
  bundle isomorphisms with `|𝒟| = |𝒟'|` and `[D] ≠ [D']`.
- `[D]_* = [D']_*`, `[D]^* = [D']^*`: the project's `GenSBMap.pushforward`, `.pullback` agree on
  `Γ(P, μ)`, resp. `Γ(P', μ')` (the project's `sectionFunctors`; off sections they carry junk).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_60
open Polyfold CategoryTheory

/-- `|𝒟| = |𝒟'|`: the orbit maps of the total spaces and of the bases agree. -/
def SameSquareB {A A' : SEP.{0}} (f f' : SBLocalization.GenSBMap A A') : Prop :=
  f.orbitMap = f'.orbitMap ∧
    EPLocalization.EPLoc.orbitMap f.base = EPLocalization.EPLoc.orbitMap f'.base

/-- Remark 10.5.5: `|𝒟| = |𝒟'|` does not force `[D] = [D']`, but it forces `[D]_* = [D']_*` and
`[D]^* = [D']^*`. -/
def B : Prop :=
  (¬ ∀ (A A' : SEP.{0}) (f f' : SBLocalization.GenSBMap A A'),
      f.IsGeneralizedIso → f'.IsGeneralizedIso → SameSquareB f f' → f = f') ∧
  (∀ (A A' : SEP.{0}) (f f' : SBLocalization.GenSBMap A A') (hf : f.IsGeneralizedIso)
      (hf' : f'.IsGeneralizedIso), SameSquareB f f' →
    (∀ s ∈ A.E.sectionFunctors,
      SBLocalization.GenSBMap.pushforward hf s = SBLocalization.GenSBMap.pushforward hf' s) ∧
    (∀ t ∈ A'.E.sectionFunctors,
      SBLocalization.GenSBMap.pullback hf t = SBLocalization.GenSBMap.pullback hf' t))

end RoundTrip.V10_60
