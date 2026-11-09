import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_60

/-! Round trip for V10_60 (2021 Remark 10.5.5, p. 508, new in the 2021 edition: `|[D]| = |[D']|`
without `[D] = [D']`).

The item lists the definitions `z3EpBundle`, `z3InvHom`, `Diagram.IsotropyRel` (vocabulary) and
eleven theorems; `A` is the conjunction of their types, universes at `0` (the example theorems
have none): `remark_10_5_5` (for every `k`: `[W ←1 W →Inv W]` and `[1_W]` over `ℤ/3 × ℝ ⇉ ℝ` are
generalized strong bundle isomorphisms with the same `|[D]|`, different base classes, and
`[Inv] ≠ [1]`), `pushforward_inv_eq_pushforward_id` (the positive half *for this example*),
`z3InvHom_mem_equivalences`, `orbitMap_ofHom_z3InvHom`, `base_orbitMap_ofHom_z3InvHom`, the
`IsotropyRel` lemmas (`isotropyRel_isotropyHom`, `IsRefinement.isotropyRel_iff`,
`Equiv.isotropyRel_iff`, `isotropyRel_id`, `not_isotropyRel_inv`) and `GenSBMap.remark_10_5_3`.

`B` = (1) *not* every two generalized strong bundle isomorphisms with the same square `|𝒟|` (both
orbit maps) are equal, and (2) for *all* generalized strong bundle isomorphisms with the same
square, `[D]_* = [D']_*` and `[D]* = [D']*` on section functors.

* `A_to_B`: (1) from `A`'s `remark_10_5_5` (at `k = 0`) with `base_orbitMap_ofHom_z3InvHom` for
  the base orbit maps.  (2) is **not in `A`**: `A` has the positive half only for the example
  (`pushforward_inv_eq_pushforward_id`).  The general statement is the last part of
  `GenSBMap.theorem_10_5_4` (item V10_59, a non-item lemma here), which proves (2) outright, not
  from the hypothesis.
* `B_to_A`: `pushforward_inv_eq_pushforward_id` from `B` (2).  The rest is not a consequence of
  `B`: `B` (1) is a non-constructive `¬ ∀` and does not name the example, and the `IsotropyRel`
  lemmas and `remark_10_5_3` are general facts.  They are re-proved outright below (the project's
  proofs, copied, from non-item project lemmas). -/

namespace RoundTrip.V10_60
open Polyfold CategoryTheory Set Function SBLocalization EPLocalization
  StrongBundleLocalizationExamples

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.StrongBundleLocalizationExamples.remark_10_5_5) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.pushforward_inv_eq_pushforward_id) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.z3InvHom_mem_equivalences) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.orbitMap_ofHom_z3InvHom) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.base_orbitMap_ofHom_z3InvHom) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isotropyRel_isotropyHom.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.IsRefinement.isotropyRel_iff.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.Equiv.isotropyRel_iff.{0}) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.isotropyRel_id) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.not_isotropyRel_inv) ∧
  (type_of% @Polyfold.SBLocalization.GenSBMap.remark_10_5_3.{0})

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundleLocalizationExamples.remark_10_5_5,
    @Polyfold.StrongBundleLocalizationExamples.pushforward_inv_eq_pushforward_id,
    @Polyfold.StrongBundleLocalizationExamples.z3InvHom_mem_equivalences,
    @Polyfold.StrongBundleLocalizationExamples.orbitMap_ofHom_z3InvHom,
    @Polyfold.StrongBundleLocalizationExamples.base_orbitMap_ofHom_z3InvHom,
    @Polyfold.EPLocalization.Diagram.isotropyRel_isotropyHom.{0},
    @Polyfold.EPLocalization.Diagram.IsRefinement.isotropyRel_iff.{0},
    @Polyfold.EPLocalization.Diagram.Equiv.isotropyRel_iff.{0},
    @Polyfold.StrongBundleLocalizationExamples.isotropyRel_id,
    @Polyfold.StrongBundleLocalizationExamples.not_isotropyRel_inv,
    @Polyfold.SBLocalization.GenSBMap.remark_10_5_3.{0}⟩

/-- (1) from `A`; (2) outright from `theorem_10_5_4` (not in `A`). -/
theorem A_to_B : A → B := by
  rintro ⟨hR, -, -, -, hbase, -⟩
  refine ⟨fun h => ?_, fun A A' f f' hf hf' hS =>
    ⟨fun s hs => ((GenSBMap.theorem_10_5_4 hf).2.2.2.2 f' hf' hS.1).1 hs,
      fun t ht => ((GenSBMap.theorem_10_5_4 hf).2.2.2.2 f' hf' hS.1).2 ht⟩⟩
  obtain ⟨h1, h2, h3, -, h5⟩ := hR 0
  exact h5 (h _ _ _ _ h1 h2 ⟨h3, hbase 0⟩)

/-! ### The conjuncts of `A` that are not consequences of `B`, re-proved outright
(the project's proofs, copied, from non-item project lemmas) -/

section IsotropyRel

universe u

variable {X Y : EP.{u}}

theorem isotropyRel_isotropyHom' (d : Diagram X Y) {x : X.Obj} {x' : Y.Obj} {z : d.A.Obj}
    (a : X.Mor) (ha : X.X.src a = d.F.obj z) (ha' : X.X.tgt a = x) (b : Y.Mor)
    (hb : Y.X.src b = d.Φ.obj z) (hb' : Y.X.tgt b = x') (g : X.X.Isotropy x) :
    d.IsotropyRel g (d.isotropyHom a ha ha' b hb hb' g) := by
  obtain ⟨k, hk, hk'⟩ := d.isotropyHom_spec a ha ha' b hb hb' g
  refine ⟨z, k, a, ha, ha', b, hb, hb', GroupoidStr.Isotropy.ext ?_,
    (GroupoidStr.Isotropy.ext hk'.symm)⟩
  rw [GroupoidStr.isotropyConj_val, EpFunctor.isotropyHom_val, hk]
  let f := X.X.homMk a ha ha'
  let γ := X.X.homMk g.val g.src_val g.tgt_val
  change (Groupoid.inv f ≫ (f ≫ γ ≫ Groupoid.inv f) ≫ f).1 = γ.1
  congr 1
  simp

theorem isRefinement_isotropyRel_iff' {d' d : Diagram X Y} (hr : d'.IsRefinement d)
    {x : X.Obj} {x' : Y.Obj} (g : X.X.Isotropy x) (g' : Y.X.Isotropy x') :
    d'.IsotropyRel g g' ↔ d.IsotropyRel g g' := by
  obtain ⟨H, hH, ⟨τ⟩, ⟨σ⟩⟩ := hr
  have kF : ∀ (z : d'.A.Obj) (k : d'.A.X.Isotropy z), d'.F.isotropyHom z k =
      X.X.isotropyConj (τ.app z) (τ.src_app z) (τ.tgt_app z)
        (d.F.isotropyHom (H.obj z) (H.isotropyHom z k)) := fun z k => τ.isotropyHom_eq z k
  have kΦ : ∀ (z : d'.A.Obj) (k : d'.A.X.Isotropy z), d'.Φ.isotropyHom z k =
      Y.X.isotropyConj (σ.app z) (σ.src_app z) (σ.tgt_app z)
        (d.Φ.isotropyHom (H.obj z) (H.isotropyHom z k)) := fun z k => σ.isotropyHom_eq z k
  constructor
  · rintro ⟨z, k, a, ha, ha', b, hb, hb', rfl, rfl⟩
    have hτ : X.X.src a = X.X.tgt (τ.app z) := ha.trans (τ.tgt_app z).symm
    have hσ : Y.X.src b = Y.X.tgt (σ.app z) := hb.trans (σ.tgt_app z).symm
    refine ⟨H.obj z, H.isotropyHom z k, X.X.comp a (τ.app z),
      (X.X.src_comp _ _ hτ).trans (τ.src_app z), (X.X.tgt_comp _ _ hτ).trans ha',
      Y.X.comp b (σ.app z), (Y.X.src_comp _ _ hσ).trans (σ.src_app z),
      (Y.X.tgt_comp _ _ hσ).trans hb', ?_, ?_⟩
    · rw [kF]; exact (GroupoidStr.isotropyConj_isotropyConj _ _ _ _ _).symm
    · rw [kΦ]; exact (GroupoidStr.isotropyConj_isotropyConj _ _ _ _ _).symm
  · rintro ⟨z, k, a, ha, ha', b, hb, hb', rfl, rfl⟩
    obtain ⟨z', c, hc, hc'⟩ := hH.exists_iso z
    obtain ⟨k₁, hk₁⟩ : ∃ k₁, k₁ = d.A.X.isotropyConj (d.A.X.inv c)
        ((d.A.X.src_inv c).trans hc') ((d.A.X.tgt_inv c).trans hc) k := ⟨_, rfl⟩
    obtain ⟨k', hk'⟩ := (hH.bijective_isotropyHom z').2 k₁
    have ek : d.A.X.isotropyConj c hc hc' k₁ = k :=
      hk₁ ▸ GroupoidStr.isotropyConj_isotropyConj_inv hc hc' k
    have hFc : X.X.src a = X.X.tgt (d.F.mor c) := by rw [ha, d.F.tgt_mor, hc']
    have hΦc : Y.X.src b = Y.X.tgt (d.Φ.mor c) := by rw [hb, d.Φ.tgt_mor, hc']
    set a₀ := X.X.comp a (d.F.mor c)
    set b₀ := Y.X.comp b (d.Φ.mor c)
    have ha₀ : X.X.src a₀ = X.X.src (τ.app z') := by
      rw [X.X.src_comp _ _ hFc, d.F.src_mor, hc, τ.src_app]; rfl
    have hb₀ : Y.X.src b₀ = Y.X.src (σ.app z') := by
      rw [Y.X.src_comp _ _ hΦc, d.Φ.src_mor, hc, σ.src_app]; rfl
    have ha₁ : X.X.src a₀ = X.X.tgt (X.X.inv (τ.app z')) := ha₀.trans (X.X.tgt_inv _).symm
    have hb₁ : Y.X.src b₀ = Y.X.tgt (Y.X.inv (σ.app z')) := hb₀.trans (Y.X.tgt_inv _).symm
    have ea : X.X.comp (X.X.comp a₀ (X.X.inv (τ.app z'))) (τ.app z') = a₀ := by
      have e := GroupoidStr.comp_inv_cancel_right (G := X.X.toGroupoidStr) ha₁
      rwa [GroupoidStr.inv_inv] at e
    have eb : Y.X.comp (Y.X.comp b₀ (Y.X.inv (σ.app z'))) (σ.app z') = b₀ := by
      have e := GroupoidStr.comp_inv_cancel_right (G := Y.X.toGroupoidStr) hb₁
      rwa [GroupoidStr.inv_inv] at e
    refine ⟨z', k', X.X.comp a₀ (X.X.inv (τ.app z')),
      by rw [X.X.src_comp _ _ ha₁, X.X.src_inv, τ.tgt_app],
      by rw [X.X.tgt_comp _ _ ha₁, X.X.tgt_comp _ _ hFc, ha'],
      Y.X.comp b₀ (Y.X.inv (σ.app z')),
      by rw [Y.X.src_comp _ _ hb₁, Y.X.src_inv, σ.tgt_app],
      by rw [Y.X.tgt_comp _ _ hb₁, Y.X.tgt_comp _ _ hΦc, hb'], ?_, ?_⟩
    · rw [kF, hk']
      refine (GroupoidStr.isotropyConj_isotropyConj _ _ _ _ _).trans ?_
      refine (GroupoidStr.isotropyConj_congr ea _ _ _).trans ?_
      rw [← ek, EpFunctor.isotropyHom_isotropyConj]
      exact (GroupoidStr.isotropyConj_isotropyConj (φ := d.F.mor c) (ψ := a)
        (by rw [d.F.src_mor, hc]) (by rw [d.F.tgt_mor, hc']) ha ha'
        (d.F.isotropyHom (H.obj z') k₁)).symm
    · rw [kΦ, hk']
      refine (GroupoidStr.isotropyConj_isotropyConj _ _ _ _ _).trans ?_
      refine (GroupoidStr.isotropyConj_congr eb _ _ _).trans ?_
      rw [← ek, EpFunctor.isotropyHom_isotropyConj]
      exact (GroupoidStr.isotropyConj_isotropyConj (φ := d.Φ.mor c) (ψ := b)
        (by rw [d.Φ.src_mor, hc]) (by rw [d.Φ.tgt_mor, hc']) hb hb'
        (d.Φ.isotropyHom (H.obj z') k₁)).symm

theorem equiv_isotropyRel_iff' {d d' : Diagram X Y} (h : Diagram.Equiv d d') {x : X.Obj}
    {x' : Y.Obj} (g : X.X.Isotropy x) (g' : Y.X.Isotropy x') :
    d.IsotropyRel g g' ↔ d'.IsotropyRel g g' :=
  let ⟨_, h₁, h₂⟩ := h
  (isRefinement_isotropyRel_iff' h₁ g g').symm.trans (isRefinement_isotropyRel_iff' h₂ g g')

end IsotropyRel

section Z3

open EpGroupoid.Examples TrivialBundle

variable (k : ℕ)

theorem z3InvHom_mem_equivalences' : SEP.equivalences (z3InvHom k) :=
  EpStrongBundle.isStrongBundleEquivalence_of_inverse (isMap_z3Inv k) (isMap_z3Inv k)
    (fun _ => rfl) (fun _ => rfl) (fun p => Prod.ext (inv_inv p.1) rfl)
    (fun p => Prod.ext (inv_inv p.1) rfl) (fun _ => rfl) (fun _ => rfl)

theorem orbitMap_ofHom_z3InvHom' :
    (SDiagram.ofHom (z3InvHom k)).orbitMap = (SDiagram.id (z3SEP k)).orbitMap := by
  rw [SDiagram.orbitMap_ofHom]
  change _ = (SDiagram.ofHom (𝟙 (z3SEP k))).orbitMap
  rw [SDiagram.orbitMap_ofHom]
  funext q
  induction q using Quotient.inductionOn with | h w => rfl

theorem base_orbitMap_ofHom_z3InvHom' :
    (SDiagram.ofHom (z3InvHom k)).base.orbitMap = (SDiagram.id (z3SEP k)).base.orbitMap :=
  SDiagram.base_orbitMap_eq_of_orbitMap_eq (orbitMap_ofHom_z3InvHom' k)

theorem isotropyRel_id' :
    (SDiagram.id (z3SEP k)).base.IsotropyRel (x := (0 : Fin 1 → ℝ)) (x' := (0 : Fin 1 → ℝ))
      z3Gen z3Gen := by
  refine ⟨(0 : Fin 1 → ℝ), z3Gen, trivialZ3EpGroupoid.unit 0, rfl, rfl,
    trivialZ3EpGroupoid.unit 0, rfl, rfl, ?_, ?_⟩ <;>
  exact GroupoidStr.Isotropy.ext (Prod.ext (by
    change (1 * Multiplicative.ofAdd (1 : ZMod 3)) * 1⁻¹ = Multiplicative.ofAdd 1
    rw [one_mul, inv_one, mul_one]) rfl)

theorem not_isotropyRel_inv' :
    ¬ (SDiagram.ofHom (z3InvHom k)).base.IsotropyRel (x := (0 : Fin 1 → ℝ))
      (x' := (0 : Fin 1 → ℝ)) z3Gen z3Gen := by
  rintro ⟨z, h, a, ha, ha', b, hb, hb', h₁, h₂⟩
  have e₁ : ((a : Multiplicative (ZMod 3) × (Fin 1 → ℝ)).1 *
      (h.val : Multiplicative (ZMod 3) × (Fin 1 → ℝ)).1) *
      (a : Multiplicative (ZMod 3) × (Fin 1 → ℝ)).1⁻¹ = Multiplicative.ofAdd 1 :=
    congrArg (fun g : trivialZ3EpGroupoid.Isotropy (0 : Fin 1 → ℝ) => g.val.1) h₁
  have e₂ : ((b : Multiplicative (ZMod 3) × (Fin 1 → ℝ)).1 *
      (h.val : Multiplicative (ZMod 3) × (Fin 1 → ℝ)).1⁻¹) *
      (b : Multiplicative (ZMod 3) × (Fin 1 → ℝ)).1⁻¹ = Multiplicative.ofAdd 1 :=
    congrArg (fun g : trivialZ3EpGroupoid.Isotropy (0 : Fin 1 → ℝ) => g.val.1) h₂
  rw [mul_comm, inv_mul_cancel_left] at e₁ e₂
  rw [e₁] at e₂
  exact absurd e₂ (by decide)

theorem remark_10_5_5' :
    (SDiagram.ofHom (z3InvHom k)).cls.IsGeneralizedIso ∧
      (SDiagram.id (z3SEP k)).cls.IsGeneralizedIso ∧
      (SDiagram.ofHom (z3InvHom k)).cls.orbitMap = (SDiagram.id (z3SEP k)).cls.orbitMap ∧
      (SDiagram.ofHom (z3InvHom k)).cls.base ≠ (SDiagram.id (z3SEP k)).cls.base ∧
      (SDiagram.ofHom (z3InvHom k)).cls ≠ (SDiagram.id (z3SEP k)).cls := by
  have hb : (SDiagram.ofHom (z3InvHom k)).cls.base ≠ (SDiagram.id (z3SEP k)).cls.base := by
    intro h
    have he := EPLocalization.EPLoc.homMk_eq_homMk_iff.1 h
    exact not_isotropyRel_inv' k ((equiv_isotropyRel_iff' he _ _).2 (isotropyRel_id' k))
  exact ⟨GenSBMap.isGeneralizedIso_ofHom (z3InvHom_mem_equivalences' k),
    GenSBMap.isGeneralizedIso_ofHom (SEP.equivalences.id_mem _), orbitMap_ofHom_z3InvHom' k, hb,
    fun h => hb (congrArg GenSBMap.base h)⟩

end Z3

theorem remark_10_5_3' {A A' : SEP.{0}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso) :
    EPLoc.IsGeneralizedIso f.base ∧ EPLoc.IsGeneralizedIso f.total ∧ IsHomeomorph f.orbitMap := by
  obtain ⟨D, rfl, hΨ⟩ := hf
  exact ⟨(EPLoc.theorem_10_3_10 D.base).1.2 hΨ.isEquivalence_base,
    (EPLoc.theorem_10_3_10 D.total).1.2 hΨ.isEquivalence,
    D.total.isHomeomorph_orbitMap hΨ.isEquivalence⟩

/-- `pushforward_inv_eq_pushforward_id` from `B` (2); the rest outright. -/
theorem B_to_A : B → A := by
  rintro ⟨-, h2⟩
  refine ⟨remark_10_5_5', fun k hf hf' s hs => ?_, z3InvHom_mem_equivalences',
    orbitMap_ofHom_z3InvHom', base_orbitMap_ofHom_z3InvHom', @isotropyRel_isotropyHom'.{0},
    @isRefinement_isotropyRel_iff'.{0}, @equiv_isotropyRel_iff'.{0}, isotropyRel_id',
    not_isotropyRel_inv', @remark_10_5_3'⟩
  exact (h2 _ _ _ _ hf hf' ⟨orbitMap_ofHom_z3InvHom' k, base_orbitMap_ofHom_z3InvHom' k⟩).1 s hs

#rt_check RoundTrip.V10_60.A_to_B [Polyfold.StrongBundleLocalizationExamples.remark_10_5_5,
  Polyfold.StrongBundleLocalizationExamples.pushforward_inv_eq_pushforward_id,
  Polyfold.StrongBundleLocalizationExamples.z3InvHom_mem_equivalences,
  Polyfold.StrongBundleLocalizationExamples.orbitMap_ofHom_z3InvHom,
  Polyfold.StrongBundleLocalizationExamples.base_orbitMap_ofHom_z3InvHom,
  Polyfold.EPLocalization.Diagram.isotropyRel_isotropyHom,
  Polyfold.EPLocalization.Diagram.IsRefinement.isotropyRel_iff,
  Polyfold.EPLocalization.Diagram.Equiv.isotropyRel_iff,
  Polyfold.StrongBundleLocalizationExamples.isotropyRel_id,
  Polyfold.StrongBundleLocalizationExamples.not_isotropyRel_inv,
  Polyfold.SBLocalization.GenSBMap.remark_10_5_3]
#rt_check RoundTrip.V10_60.B_to_A [Polyfold.StrongBundleLocalizationExamples.remark_10_5_5,
  Polyfold.StrongBundleLocalizationExamples.pushforward_inv_eq_pushforward_id,
  Polyfold.StrongBundleLocalizationExamples.z3InvHom_mem_equivalences,
  Polyfold.StrongBundleLocalizationExamples.orbitMap_ofHom_z3InvHom,
  Polyfold.StrongBundleLocalizationExamples.base_orbitMap_ofHom_z3InvHom,
  Polyfold.EPLocalization.Diagram.isotropyRel_isotropyHom,
  Polyfold.EPLocalization.Diagram.IsRefinement.isotropyRel_iff,
  Polyfold.EPLocalization.Diagram.Equiv.isotropyRel_iff,
  Polyfold.StrongBundleLocalizationExamples.isotropyRel_id,
  Polyfold.StrongBundleLocalizationExamples.not_isotropyRel_inv,
  Polyfold.SBLocalization.GenSBMap.remark_10_5_3]
#rt_overlap RoundTrip.V10_60.B_to_A [Polyfold.StrongBundleLocalizationExamples.remark_10_5_5,
  Polyfold.StrongBundleLocalizationExamples.pushforward_inv_eq_pushforward_id,
  Polyfold.StrongBundleLocalizationExamples.z3InvHom_mem_equivalences,
  Polyfold.StrongBundleLocalizationExamples.orbitMap_ofHom_z3InvHom,
  Polyfold.StrongBundleLocalizationExamples.base_orbitMap_ofHom_z3InvHom,
  Polyfold.EPLocalization.Diagram.isotropyRel_isotropyHom,
  Polyfold.EPLocalization.Diagram.IsRefinement.isotropyRel_iff,
  Polyfold.EPLocalization.Diagram.Equiv.isotropyRel_iff,
  Polyfold.StrongBundleLocalizationExamples.isotropyRel_id,
  Polyfold.StrongBundleLocalizationExamples.not_isotropyRel_inv,
  Polyfold.SBLocalization.GenSBMap.remark_10_5_3]

end RoundTrip.V10_60
