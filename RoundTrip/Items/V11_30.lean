import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_30

/-! Round trip for V11_30 (2021 §11.5, Proposition 11.5.1, p. 547: auxiliary norms along
generalized strong bundle isomorphisms).

The item lists eight definitions (`GenSBMap.pullNorm`, `pushNorm`, `SDiagram.pullNorm`,
`pushNorm`, `SDiagram.oneOrbitMap`, `oneToOrbit`, `oneMap`, `IsOneInvariant`; vocabulary) and
twenty theorems; `A` is the conjunction of the theorems' types, universes at `0`:
`GenSBMap.proposition_11_5_1` (independence of the representative, the text's formula
`N(e) = N'(Ψ(e''))` for `Φ(e'') ≅ e`, continuity and condition (3) of Definition 8.3.5 for
auxiliary norms, mutually inverse on invariant functions, dependence on `|[D]|` only) and the
nineteen supporting lemmas on `pullNorm`, `oneOrbitMap`, `oneToOrbit`, `oneMap`, `IsOneInvariant`
(mostly for arbitrary or merely invariant `N`).

`B`: (1) `[D]^*N'`, `[D]_*N` are auxiliary norms (`EpStrongBundle.IsAuxNorm`) for auxiliary norms
`N'`, `N`; (2) `FormulaB`: the formulas `N'(Ψ(e''))` and `N(Φ(e''))` for every representative
and every choice of `e''`; (3) mutually inverse; (4) depend only on `|[D]|`.

* `A → B` fails at one point: in (1), `IsAuxNorm` contains Part I's conditions (1) (a complete
  norm on every fibre, `fiber`) and (2) (`P(w_k) → x`, `N(w_k) → 0` ⇒ `w_k → 0_x`,
  `tendsto_zeroOne`) for the transported functions; `A` proves only continuity and condition (3)
  (`map_μ`), and the project's header says (1), (2) are not formalized (they need the level-`1`
  fibre maps of `μ` and of a strong bundle equivalence as linear homeomorphisms).
  `A_to_BPart` proves the rest of `B` from `A`: continuity and condition (3) in (1), all of
  `FormulaB`, (3) and (4).  `BPart_and_aux_iff_B` shows that the missing content is exactly
  `fiber ∧ tendsto_zeroOne` of `[D]^*N'` and `[D]_*N`.
* `B → A` fails: `A`'s conjuncts concern arbitrary functions `N'` (independence of the
  representative, `pullNorm_eq_of_orbitMap_eq`, `pullNorm_eq_lift`), invariant functions
  (inverses, `pullNorm_eq`), or no norm at all (`oneOrbitMap`, `oneToOrbit`, `oneMap` lemmas),
  while `B` only speaks about auxiliary norms.  Re-proving `A` outright would not use `B`
  (vacuous), so no `B_to_A` is given. -/

namespace RoundTrip.V11_30
open Polyfold Polyfold.SBLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.GenSBMap.proposition_11_5_1.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pullNorm_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pullNorm_eq_Ψ.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.isOneInvariant_pullNorm.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pullNorm_eq_lift.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.continuous_pullNorm.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pushNorm_pullNorm.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pullNorm_pushNorm.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pullNorm_eq_of_orbitMap_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pushNorm_eq_of_orbitMap_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.continuous_oneOrbitMap.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.oneOrbitMap_oneMap.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.oneToOrbit_oneOrbitMap.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.oneOrbitMap_eq_of_orbitMap_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.oneToOrbit_injective.{0}) ∧
  (type_of% @Polyfold.SBLocalization.continuous_oneMap.{0}) ∧
  (type_of% @Polyfold.SBLocalization.oneToOrbit_oneMap.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isOneInvariant_const.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isOneInvariant_iff.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsAuxNorm.isOneInvariant.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.GenSBMap.proposition_11_5_1.{0},
    @Polyfold.SBLocalization.SDiagram.pullNorm_eq.{0},
    @Polyfold.SBLocalization.SDiagram.pullNorm_eq_Ψ.{0},
    @Polyfold.SBLocalization.SDiagram.isOneInvariant_pullNorm.{0},
    @Polyfold.SBLocalization.SDiagram.pullNorm_eq_lift.{0},
    @Polyfold.SBLocalization.SDiagram.continuous_pullNorm.{0},
    @Polyfold.SBLocalization.SDiagram.pushNorm_pullNorm.{0},
    @Polyfold.SBLocalization.SDiagram.pullNorm_pushNorm.{0},
    @Polyfold.SBLocalization.SDiagram.pullNorm_eq_of_orbitMap_eq.{0},
    @Polyfold.SBLocalization.SDiagram.pushNorm_eq_of_orbitMap_eq.{0},
    @Polyfold.SBLocalization.SDiagram.continuous_oneOrbitMap.{0},
    @Polyfold.SBLocalization.SDiagram.oneOrbitMap_oneMap.{0},
    @Polyfold.SBLocalization.SDiagram.oneToOrbit_oneOrbitMap.{0},
    @Polyfold.SBLocalization.SDiagram.oneOrbitMap_eq_of_orbitMap_eq.{0},
    @Polyfold.SBLocalization.oneToOrbit_injective.{0},
    @Polyfold.SBLocalization.continuous_oneMap.{0},
    @Polyfold.SBLocalization.oneToOrbit_oneMap.{0},
    @Polyfold.SBLocalization.isOneInvariant_const.{0},
    @Polyfold.SBLocalization.isOneInvariant_iff.{0},
    @Polyfold.EpStrongBundle.IsAuxNorm.isOneInvariant.{0}⟩

/-! ### `A → B` without conditions (1), (2) of Definition 8.3.5 -/

/-- What `A` says of `[D]^*N'` in place of `IsAuxNorm`: continuity and condition (3). -/
def ContMapμB (A : SEP.{0}) (N : StrongBundle.One A.B → ℝ) : Prop :=
  Continuous N ∧ ∀ (h k : StrongBundle.One A.B) (φ : A.Mor)
    (hk : A.P (StrongBundle.oneVal A.B k) = A.X.src φ),
    StrongBundle.oneVal A.B h = A.E.μ ⟨(φ, StrongBundle.oneVal A.B k), hk⟩ → N h = N k

/-- `B` with "is an auxiliary norm" in the conclusion of (1) weakened to `ContMapμB`. -/
def BPart : Prop :=
  (∀ (A A' : SEP.{0}) (f : GenSBMap A A') (hf : f.IsGeneralizedIso),
    (∀ N' : StrongBundle.One A'.B → ℝ, A'.E.IsAuxNorm N' →
      ContMapμB A (GenSBMap.pullNorm hf N')) ∧
    (∀ N : StrongBundle.One A.B → ℝ, A.E.IsAuxNorm N →
      ContMapμB A' (GenSBMap.pushNorm hf N))) ∧
  FormulaB ∧
  (∀ (A A' : SEP.{0}) (f : GenSBMap A A') (hf : f.IsGeneralizedIso),
    (∀ N' : StrongBundle.One A'.B → ℝ, A'.E.IsAuxNorm N' →
      GenSBMap.pushNorm hf (GenSBMap.pullNorm hf N') = N') ∧
    (∀ N : StrongBundle.One A.B → ℝ, A.E.IsAuxNorm N →
      GenSBMap.pullNorm hf (GenSBMap.pushNorm hf N) = N)) ∧
  (∀ (A A' : SEP.{0}) (f₁ f₂ : GenSBMap A A') (h₁ : f₁.IsGeneralizedIso)
    (h₂ : f₂.IsGeneralizedIso), f₁.orbitMap = f₂.orbitMap →
    (∀ N' : StrongBundle.One A'.B → ℝ, A'.E.IsAuxNorm N' →
      GenSBMap.pullNorm h₁ N' = GenSBMap.pullNorm h₂ N') ∧
    (∀ N : StrongBundle.One A.B → ℝ, A.E.IsAuxNorm N →
      GenSBMap.pushNorm h₁ N = GenSBMap.pushNorm h₂ N))

theorem A_to_BPart : A → BPart := by
  rintro ⟨hprop, -, hΨf, -, -, -, -, -, -, -, -, -, -, -, hinj, -, hone, -, -, hinv⟩
  -- `oneMap Φ ⟦e''⟧ = ⟦e⟧` from a morphism `Φ(e'') → e`
  have hmk : ∀ {A₀ A₁ : SEP.{0}} (Φ : A₀ ⟶ A₁) (e'' : StrongBundle.One A₀.B)
      (e : StrongBundle.One A₁.B),
      A₁.E.toEpGroupoid.Isomorphic (Φ.Φ.obj (StrongBundle.oneVal A₀.B e''))
        (StrongBundle.oneVal A₁.B e) → oneMap Φ ⟦e''⟧ = ⟦e⟧ := by
    intro A₀ A₁ Φ e'' e h
    apply hinj
    rw [hone, oneToOrbit_mk, oneToOrbit_mk, GroupoidFunctor.orbitMap_π]
    exact (GroupoidStr.π_eq_π_iff _).2 h
  refine ⟨fun A A' f hf => ⟨fun N' hN' => (hprop hf).2.2.2.1 N' hN',
      fun N hN => (hprop hf).2.2.2.2.1 N hN⟩, ?_,
    fun A A' f hf => ⟨fun N' hN' => (hprop hf).2.2.2.2.2.2.1 N' (hinv hN'),
      fun N hN => (hprop hf).2.2.2.2.2.1 N (hinv hN)⟩,
    fun A A' f₁ f₂ h₁ h₂ h => ⟨fun N' _ => ((hprop h₁).2.2.2.2.2.2.2 h₂ h).1 N',
      fun N _ => ((hprop h₁).2.2.2.2.2.2.2 h₂ h).2 N⟩⟩
  intro A A' f hf D hΨ hD
  refine ⟨fun N' hN' e e'' e' hiso he' => ?_, fun N hN e' e'' e hiso he => ?_⟩
  · rw [(hprop hf).2.2.1 D hD N' (hinv hN') e e'' (hmk D.Φ e'' e hiso)]
    exact hinv hN' _ _ (congrArg A'.E.toEpGroupoid.π he'.symm)
  · rw [(hprop hf).2.1 D hΨ hD N]
    change (D.symm hΨ).pullNorm N e' = N e
    rw [hΨf (D := D.symm hΨ) (hinv hN) e'' (hmk D.Ψ e'' e' hiso)]
    exact hinv hN _ _ (congrArg A.E.toEpGroupoid.π he.symm)

/-- `B` is exactly `BPart` plus Part I's conditions (1), (2) (`fiber`, `tendsto_zeroOne`) for
`[D]^*N'` and `[D]_*N`. -/
theorem BPart_and_aux_iff_B :
    (BPart ∧ ∀ (A A' : SEP.{0}) (f : GenSBMap A A') (hf : f.IsGeneralizedIso),
      (∀ N' : StrongBundle.One A'.B → ℝ, A'.E.IsAuxNorm N' →
        (∀ x, A.B.IsCompleteFiberNorm (GenSBMap.pullNorm hf N') x) ∧
        ∀ (w : ℕ → StrongBundle.One A.B) (x : A.Obj),
          Filter.Tendsto (fun k => A.P (StrongBundle.oneVal A.B (w k))) Filter.atTop (nhds x) →
          Filter.Tendsto (fun k => GenSBMap.pullNorm hf N' (w k)) Filter.atTop (nhds 0) →
          Filter.Tendsto w Filter.atTop (nhds (A.B.zeroOne x))) ∧
      (∀ N : StrongBundle.One A.B → ℝ, A.E.IsAuxNorm N →
        (∀ x, A'.B.IsCompleteFiberNorm (GenSBMap.pushNorm hf N) x) ∧
        ∀ (w : ℕ → StrongBundle.One A'.B) (x : A'.Obj),
          Filter.Tendsto (fun k => A'.P (StrongBundle.oneVal A'.B (w k))) Filter.atTop (nhds x) →
          Filter.Tendsto (fun k => GenSBMap.pushNorm hf N (w k)) Filter.atTop (nhds 0) →
          Filter.Tendsto w Filter.atTop (nhds (A'.B.zeroOne x)))) ↔ B := by
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, haux⟩
    refine ⟨fun A A' f hf => ⟨fun N' hN' => ?_, fun N hN => ?_⟩, h2, h3, h4⟩
    · obtain ⟨hc, hμ⟩ := (h1 A A' f hf).1 N' hN'
      obtain ⟨hfib, ht⟩ := (haux A A' f hf).1 N' hN'
      exact ⟨⟨hc, hfib, ht⟩, hμ⟩
    · obtain ⟨hc, hμ⟩ := (h1 A A' f hf).2 N hN
      obtain ⟨hfib, ht⟩ := (haux A A' f hf).2 N hN
      exact ⟨⟨hc, hfib, ht⟩, hμ⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨fun A A' f hf => ⟨fun N' hN' => ?_, fun N hN => ?_⟩, h2, h3, h4⟩,
      fun A A' f hf => ⟨fun N' hN' => ?_, fun N hN => ?_⟩⟩
    · have h := (h1 A A' f hf).1 N' hN'
      exact ⟨h.isAuxNorm.continuous, h.map_μ⟩
    · have h := (h1 A A' f hf).2 N hN
      exact ⟨h.isAuxNorm.continuous, h.map_μ⟩
    · have h := (h1 A A' f hf).1 N' hN'
      exact ⟨h.isAuxNorm.fiber, h.isAuxNorm.tendsto_zeroOne⟩
    · have h := (h1 A A' f hf).2 N hN
      exact ⟨h.isAuxNorm.fiber, h.isAuxNorm.tendsto_zeroOne⟩

#rt_check RoundTrip.V11_30.A_to_BPart [Polyfold.SBLocalization.GenSBMap.proposition_11_5_1,
  Polyfold.SBLocalization.SDiagram.pullNorm_eq, Polyfold.SBLocalization.SDiagram.pullNorm_eq_Ψ,
  Polyfold.SBLocalization.SDiagram.isOneInvariant_pullNorm,
  Polyfold.SBLocalization.SDiagram.pullNorm_eq_lift,
  Polyfold.SBLocalization.SDiagram.continuous_pullNorm,
  Polyfold.SBLocalization.SDiagram.pushNorm_pullNorm,
  Polyfold.SBLocalization.SDiagram.pullNorm_pushNorm,
  Polyfold.SBLocalization.SDiagram.pullNorm_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.SDiagram.pushNorm_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.SDiagram.continuous_oneOrbitMap,
  Polyfold.SBLocalization.SDiagram.oneOrbitMap_oneMap,
  Polyfold.SBLocalization.SDiagram.oneToOrbit_oneOrbitMap,
  Polyfold.SBLocalization.SDiagram.oneOrbitMap_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.oneToOrbit_injective, Polyfold.SBLocalization.continuous_oneMap,
  Polyfold.SBLocalization.oneToOrbit_oneMap, Polyfold.SBLocalization.isOneInvariant_const,
  Polyfold.SBLocalization.isOneInvariant_iff, Polyfold.EpStrongBundle.IsAuxNorm.isOneInvariant]
#rt_check RoundTrip.V11_30.BPart_and_aux_iff_B [Polyfold.SBLocalization.GenSBMap.proposition_11_5_1,
  Polyfold.SBLocalization.SDiagram.pullNorm_eq, Polyfold.SBLocalization.SDiagram.pullNorm_eq_Ψ,
  Polyfold.SBLocalization.SDiagram.isOneInvariant_pullNorm,
  Polyfold.SBLocalization.SDiagram.pullNorm_eq_lift,
  Polyfold.SBLocalization.SDiagram.continuous_pullNorm,
  Polyfold.SBLocalization.SDiagram.pushNorm_pullNorm,
  Polyfold.SBLocalization.SDiagram.pullNorm_pushNorm,
  Polyfold.SBLocalization.SDiagram.pullNorm_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.SDiagram.pushNorm_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.SDiagram.continuous_oneOrbitMap,
  Polyfold.SBLocalization.SDiagram.oneOrbitMap_oneMap,
  Polyfold.SBLocalization.SDiagram.oneToOrbit_oneOrbitMap,
  Polyfold.SBLocalization.SDiagram.oneOrbitMap_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.oneToOrbit_injective, Polyfold.SBLocalization.continuous_oneMap,
  Polyfold.SBLocalization.oneToOrbit_oneMap, Polyfold.SBLocalization.isOneInvariant_const,
  Polyfold.SBLocalization.isOneInvariant_iff, Polyfold.EpStrongBundle.IsAuxNorm.isOneInvariant]

end RoundTrip.V11_30
