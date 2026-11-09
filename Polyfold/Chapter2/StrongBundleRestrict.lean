import Polyfold.Chapter2.StrongBundleOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.5,
Definitions 2.6.4–2.6.5 (preprint 2.50–2.51) (strong bundle charts, atlases, their equivalence, and "an equivalence class
of strong bundle atlases"); §2.2, Definition 2.3.3 (preprint 2.12) (equivalence of M-polyfold atlases).

# Restriction of strong bundle charts; equivalence of strong bundle atlases

## The text, paraphrased

(Definition 2.6.4 (preprint 2.50)) A strong bundle chart `(Φ, P⁻¹(V), K, U ◁ F)` is a homeomorphism
`Φ : P⁻¹(V) → K` covering a homeomorphism `φ : V → O`, linear on the fibres; two charts are
compatible if `(Φ' ∘ Φ⁻¹)[i]` are sc-diffeomorphisms for `i = 0, 1`; two strong bundle atlases are
equivalent if their union is an atlas.  (Definition 2.6.5 (preprint 2.51)) A strong bundle is `P : Y → X` with "an
equivalence class of strong bundle atlases".  (Definition 2.3.3 (preprint 2.12)) The same for M-polyfold atlases.

## What is formalized

* **Restriction of a strong bundle chart** to an open subset `s` of the domain `V` of its base
  chart (as `MChart.restrict` does for M-polyfold charts): `Polyfold.StrongBundleChart.restrict`,
  over the base chart `φ|s`, with the strong bundle retraction restricted to
  `(U ∩ r⁻¹(W)) ◁ F` (`IsStrongBundleRetraction.restrict`, `φ(s) = O ∩ W`), and its API
  (`restrict_apply`, `restrict_source`, `restrict_K`: `K_s = {(u, h) ∈ K | u ∈ φ(s)}`,
  `restrict_U`: the domain `{u ∈ U | r(u) ∈ φ(s)}` does not depend on `W`, `liftOne_restrict`).
* `StrongBundleChart.Compatible.restrict_left`, `restrict_right`, `restrict`: **compatibility
  passes to restrictions**.
* `StrongBundleChart.compatible_of_locally`: **compatibility of strong bundle charts is local** —
  if `c` and `c'` are compatible with every chart of a family covering `P⁻¹(V ∩ V')`, they are
  compatible (on `[0]` and `[1]`, with the `F₁`-conditions); the analogue of
  `MChart.compatible_of_locally`.
* `StrongBundleAtlas.equiv_iff` (equivalence is pairwise compatibility),
  `StrongBundleAtlas.Equiv.refl`, `.symm`, `.trans` and `StrongBundleAtlas.equivalence`:
  **equivalence of strong bundle atlases is an equivalence relation** (Definition 2.6.5 (preprint 2.51)'s
  "equivalence class").  Likewise `MAtlas.Equiv.trans`, `MAtlas.equivalence` for M-polyfold atlases
  (Definition 2.3.3 (preprint 2.12)/2.13; the project had `refl` and `symm` only).
* Overlaps without continuity of `P`: `StrongBundleChart.image_preimage_eq`
  (`Φ(P⁻¹(t)) = K ∩ (W × F)` for `t ⊆ V` open, `φ(t) = O ∩ W`), `isScRetract_overlap'`,
  `isScRetract_overlap_one'`.

## What the text leaves implicit, and the choices made

* That atlas equivalence is transitive (needed for "equivalence class") is not discussed in the
  text, for strong bundle atlases nor for M-polyfold atlases.  It rests on the locality of
  compatibility: near a point of `Φ(P⁻¹(V ∩ V''))` the transition `Φ'' ∘ Φ⁻¹` factors through a
  chart `Φ'` of the middle atlas, on `[0]` and on `[1]` (Theorem 2.1.15 (preprint 2.8) and the locality of
  sc-smoothness between retracts), and the `F₁`-condition of the `[1]`-transition (Findings,
  Chapter 2, item 11) passes through the factorization.
* Nothing here uses the continuity of `P` (the text's `P` is continuous, but `StrongBundleAtlas`
  does not ask for it): the overlaps `Φ(P⁻¹(V ∩ V'))` are open in `K` through the base chart,
  `= K ∩ (W × F)`.  These results answer round-trip items V2.58 (a) and V5.4.
* The restricted chart is defined with an open `W ⊆ E` such that `φ(s) = O ∩ W`, chosen once and
  for all (`StrongBundleChart.restrictOpen`); the restricted retraction has domain
  `U ∩ r⁻¹(W) = {u ∈ U | r(u) ∈ φ(s)}`, which does not depend on the choice (`restrict_U`).
* That a restricted chart of a strong bundle `P` is again a chart of `P`, and that the charts of
  `P` (`StrongBundle.IsChart`) depend only on the equivalence class of the atlas, are in
  `Polyfold/Chapter3/StrongBundleMaximalAtlas.lean` (where `StrongBundle.IsChart` is available).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

/-! ### Equivalence of M-polyfold atlases is transitive -/

namespace MAtlas

variable {X : Type u} [TopologicalSpace X]

/-- **Equivalence of M-polyfold atlases is transitive** (Definition 2.3.3 (preprint 2.12); needed for "an
equivalence class of atlases", Definition 2.3.4 (preprint 2.13)): by the locality of compatibility through the
charts of the middle atlas (`MChart.compatible_of_locally`). -/
theorem Equiv.trans {A B C : MAtlas X} (hAB : A.Equiv B) (hBC : B.Equiv C) : A.Equiv C := by
  rw [MAtlas.equiv_iff] at hAB hBC ⊢
  intro φ hφ ψ hψ
  exact MChart.compatible_of_locally φ ψ B.charts (fun χ hχ => hAB φ hφ χ hχ)
    (fun χ hχ => hBC χ hχ ψ hψ) fun x _ => B.cover x

/-- **Equivalence of M-polyfold atlases is an equivalence relation** (Definition 2.3.3 (preprint 2.12)). -/
theorem equivalence : Equivalence (MAtlas.Equiv (X := X)) :=
  ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

end MAtlas

/-! ### Restriction of strong bundle retractions -/

section RetractionRestrict

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **The restriction of a strong bundle retraction** `R(u, h) = (r(u), Γ(u, h))` on `U ◁ F` to
`(U ∩ r⁻¹(W)) ◁ F`, `W` open: again a strong bundle retraction (its base retraction is the
restriction `r|U ∩ r⁻¹(W)` of Proposition 2.3.1 (preprint 2.10) (1), `ScRetraction.restrict`). -/
theorem IsStrongBundleRetraction.restrict (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) {W : Set (E 0)} (hW : IsOpen W) :
    IsStrongBundleRetraction ((hR.baseRetraction hU).restrict hW).U R where
  mapsTo p hp := by
    refine ⟨?_, mem_univ _⟩
    have h1 := hR.apply_fst hp.1.1 p.2
    rw [Prod.mk.eta] at h1
    rw [h1]
    exact ((hR.baseRetraction hU).restrict hW).mapsTo hp.1
  fst_independent u hu := hR.fst_independent u hu.1
  fiber_linear u hu := hR.fiber_linear u hu.1
  preserves_filtration m k hk u hu := hR.preserves_filtration m k hk u hu.1
  isScSmooth_zero := hR.isScSmooth_zero.of_subset
    (((hR.baseRetraction hU).restrict hW).relOpen.prod_univ F).isScDomain
    (prod_mono (fun _ hu => hu.1) subset_rfl)
  isScSmooth_one := hR.isScSmooth_one.of_subset
    (((hR.baseRetraction hU).restrict hW).relOpen.prod_univ F.shift).isScDomain
    (prod_mono (fun _ hu => hu.1) subset_rfl)
  idem p hp := hR.idem p ⟨hp.1.1, mem_univ _⟩

/-- The base retract of the restricted strong bundle retraction is `r(U) ∩ W`. -/
lemma IsStrongBundleRetraction.restrict_base_retract (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) {W : Set (E 0)} (hW : IsOpen W) :
    ((hR.restrict hU hW).baseRetraction ((hR.baseRetraction hU).restrict hW).relOpen).retract =
      (hR.baseRetraction hU).retract ∩ W :=
  (hR.baseRetraction hU).restrict_retract hW

/-- `K[1]` of `K ∩ (W × F)` is `K[1] ∩ (W × F¹)`. -/
lemma strongShiftOne_inter_prod (K : Set (E 0 × F 0)) (W : Set (E 0)) :
    strongShiftOne (K ∩ (W ×ˢ univ)) = strongShiftOne K ∩ (W ×ˢ (univ : Set (F.shift 0))) :=
  rfl

end RetractionRestrict

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundleChart

/-! ### Pieces `Φ(P⁻¹(t))` of a strong bundle chart and its overlaps -/

section Pieces

variable (c : StrongBundleChart PX P)

/-- `y ∈ P⁻¹(V)` when `P(y) ∈ V`. -/
lemma mem_source_of_mem_base {y : Y} (hy : P y ∈ c.φ.source) : y ∈ c.toPartialEquiv.source := by
  rw [c.source_eq]; exact hy

/-- `P(y) ∈ V` for `y ∈ P⁻¹(V)`. -/
lemma mem_base_of_mem_source {y : Y} (hy : y ∈ c.toPartialEquiv.source) : P y ∈ c.φ.source := by
  rw [c.source_eq] at hy; exact hy

/-- The base point of a point of `K` lies in `O`. -/
lemma fst_mem_model_O {k : c.φ.model.E 0 × c.F 0} (hk : k ∈ c.K) : k.1 ∈ c.φ.model.O := by
  rw [← c.base_K]; exact ⟨k, hk, rfl⟩

/-- A point of `K` is fixed by the strong bundle retraction. -/
lemma R_eq_self_of_mem_K {k : c.φ.model.E 0 × c.F 0} (hk : k ∈ c.K) : c.R k = k := by
  obtain ⟨q, hq, rfl⟩ := hk
  exact c.isRetraction.idem q hq

/-- **The part of a strong bundle chart over an open subset of the base**: for `t ⊆ V` with
`φ(t) = O ∩ W`, `Φ(P⁻¹(t)) = K ∩ (W × F)` (no continuity of `P` is needed). -/
lemma image_preimage_eq {t : Set X} (ht : t ⊆ c.φ.source) {W : Set (c.φ.model.E 0)}
    (hW : c.φ '' t = c.φ.model.O ∩ W) :
    c.toPartialEquiv '' (P ⁻¹' t) = c.K ∩ (W ×ˢ univ) := by
  ext k
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hys : y ∈ c.toPartialEquiv.source := c.mem_source_of_mem_base (ht hy)
    refine ⟨?_, ?_, mem_univ _⟩
    · rw [← c.image_source]; exact ⟨y, hys, rfl⟩
    · have h1 : c.φ (P y) ∈ c.φ '' t := ⟨P y, hy, rfl⟩
      rw [hW] at h1
      rw [c.covers y hys]; exact h1.2
  · rintro ⟨hk, hkW, -⟩
    have hk' : k ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hk
    have hys : c.toPartialEquiv.symm k ∈ c.toPartialEquiv.source := c.toPartialEquiv.map_target hk'
    have hcy : c.toPartialEquiv (c.toPartialEquiv.symm k) = k := c.toPartialEquiv.right_inv hk'
    refine ⟨_, ?_, hcy⟩
    have hPy := c.mem_base_of_mem_source hys
    have h1 : c.φ (P (c.toPartialEquiv.symm k)) ∈ c.φ '' t := by
      rw [hW, ← c.covers _ hys, hcy]; exact ⟨c.fst_mem_model_O hk, hkW⟩
    obtain ⟨x, hx, hxe⟩ := h1
    have := c.φ.toPartialEquiv.injOn (ht hx) hPy hxe
    change P (c.toPartialEquiv.symm k) ∈ t
    rw [← this]; exact hx

/-- The overlap `Φ(P⁻¹(V ∩ V'))` as the part of `Φ` over `V ∩ V'`. -/
lemma overlap_eq_image_preimage (c' : StrongBundleChart PX P) :
    c.overlap c' = c.toPartialEquiv '' (P ⁻¹' (c.φ.source ∩ c'.φ.source)) := by
  rw [StrongBundleChart.overlap, c.source_eq, c'.source_eq, preimage_inter]

/-- The overlap `Φ(P⁻¹(V ∩ V'))` is `K ∩ (W × F)` for an open `W` (no continuity of `P`). -/
lemma exists_overlap_eq (c' : StrongBundleChart PX P) :
    ∃ W : Set (c.φ.model.E 0), IsOpen W ∧ c.overlap c' = c.K ∩ (W ×ˢ univ) := by
  obtain ⟨W, hW, hWeq⟩ := c.φ.exists_isOpen_image_eq (s := c.φ.source ∩ c'.φ.source)
    inter_subset_left (c.φ.isOpen_source.inter c'.φ.isOpen_source)
  exact ⟨W, hW, by rw [c.overlap_eq_image_preimage, c.image_preimage_eq inter_subset_left hWeq]⟩

/-- The part `Φ(P⁻¹(t))` over an open `t ⊆ V` is a retract, `[0]`. -/
lemma isScRetract_image_preimage {t : Set X} (ht : t ⊆ c.φ.source) (hto : IsOpen t) :
    IsScRetract (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) (c.toPartialEquiv '' (P ⁻¹' t)) := by
  obtain ⟨W, hW, hWeq⟩ := c.φ.exists_isOpen_image_eq ht hto
  rw [c.image_preimage_eq ht hWeq]
  exact proposition_2_3_1_one c.isScRetract (hW.prod isOpen_univ)

/-- The part `Φ(P⁻¹(t))[1]` over an open `t ⊆ V` is a retract, `[1]`. -/
lemma isScRetract_one_image_preimage {t : Set X} (ht : t ⊆ c.φ.source) (hto : IsOpen t) :
    IsScRetract (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
      (strongShiftOne (c.toPartialEquiv '' (P ⁻¹' t))) := by
  obtain ⟨W, hW, hWeq⟩ := c.φ.exists_isOpen_image_eq ht hto
  rw [c.image_preimage_eq ht hWeq, strongShiftOne_inter_prod]
  exact proposition_2_3_1_one c.isScRetract_one (hW.prod isOpen_univ)

/-- Overlaps of strong bundle charts are retracts, `[0]`, without continuity of `P` (compare
`StrongBundleChart.isScRetract_overlap`). -/
lemma isScRetract_overlap' (c' : StrongBundleChart PX P) :
    IsScRetract (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) (c.overlap c') := by
  rw [c.overlap_eq_image_preimage]
  exact c.isScRetract_image_preimage inter_subset_left (c.φ.isOpen_source.inter c'.φ.isOpen_source)

/-- Overlaps of strong bundle charts are retracts, `[1]`, without continuity of `P` (compare
`StrongBundleChart.isScRetract_overlap_one`). -/
lemma isScRetract_overlap_one' (c' : StrongBundleChart PX P) :
    IsScRetract (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
      (strongShiftOne (c.overlap c')) := by
  rw [c.overlap_eq_image_preimage]
  exact c.isScRetract_one_image_preimage inter_subset_left
    (c.φ.isOpen_source.inter c'.φ.isOpen_source)

/-- For `t ⊆ V ∩ V'` with `φ(t) = O ∩ W`: `Φ(P⁻¹(V ∩ V')) ∩ (W × F) = Φ(P⁻¹(t))`. -/
lemma overlap_inter_eq {c' : StrongBundleChart PX P} {t : Set X}
    (ht : t ⊆ c.φ.source ∩ c'.φ.source) {W : Set (c.φ.model.E 0)}
    (hW : c.φ '' t = c.φ.model.O ∩ W) :
    c.overlap c' ∩ (W ×ˢ univ) = c.toPartialEquiv '' (P ⁻¹' t) := by
  have he := c.image_preimage_eq (ht.trans inter_subset_left) hW
  apply Subset.antisymm
  · rw [he]; exact inter_subset_inter_left _ (c.overlap_subset_K c')
  · intro k hk
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hy, rfl⟩ := hk
      rw [c.overlap_eq_image_preimage]; exact ⟨y, ht hy, rfl⟩
    · rw [he] at hk; exact hk.2

/-- The part of `Φ'` over `t` contains the image of the part of `Φ` under `Φ' ∘ Φ⁻¹`. -/
lemma transition_mapsTo_image_preimage (c' : StrongBundleChart PX P) {t : Set X}
    (ht : t ⊆ c.φ.source ∩ c'.φ.source) :
    MapsTo (c.transition c') (c.toPartialEquiv '' (P ⁻¹' t)) (c'.toPartialEquiv '' (P ⁻¹' t)) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [c.transition_apply c' (c.mem_source_of_mem_base (ht hy).1)]
  exact ⟨y, hy, rfl⟩

/-- `Φ' ∘ Φ⁻¹` maps the overlap `Φ(P⁻¹(V ∩ V'))` onto `Φ'(P⁻¹(V ∩ V'))`. -/
lemma transition_mapsTo (c' : StrongBundleChart PX P) :
    MapsTo (c.transition c') (c.overlap c') (c'.overlap c) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [c.transition_apply c' hy.1]
  exact ⟨y, ⟨hy.2, hy.1⟩, rfl⟩

/-- The `[1]`-transition at a point `p` with `(p₁, ι p₂) = Φ(y)`. -/
lemma shiftFiber_transition_eq (c' : StrongBundleChart PX P) {p : (c.φ.model.E.prod c.F.shift) 0}
    {y : Y} (hys : y ∈ c.toPartialEquiv.source) (hp : (p.1, c.F.toBase 1 p.2) = c y) :
    shiftFiber (c.transition c') p =
      ((c' y).1, Function.invFun (c'.F.toBase 1) (c' y).2) := by
  change ((c.transition c' (p.1, c.F.toBase 1 p.2)).1,
    Function.invFun (c'.F.toBase 1) (c.transition c' (p.1, c.F.toBase 1 p.2)).2) = _
  rw [hp, c.transition_apply c' hys]

/-- Under the `F₁`-condition at `Φ'(y)`, the `[1]`-transition of `p` with `(p₁, ι p₂) = Φ(y)`
lies over `Φ'(y)`. -/
lemma toBase_shiftFiber_transition (c' : StrongBundleChart PX P)
    {p : (c.φ.model.E.prod c.F.shift) 0} {y : Y} (hys : y ∈ c.toPartialEquiv.source)
    (hp : (p.1, c.F.toBase 1 p.2) = c y) (h1 : (c' y).2 ∈ range (c'.F.toBase 1)) :
    ((shiftFiber (c.transition c') p).1, c'.F.toBase 1 (shiftFiber (c.transition c') p).2) =
      c' y := by
  rw [c.shiftFiber_transition_eq c' hys hp, Function.invFun_eq h1]

/-- The `[1]`-transition maps `Φ(P⁻¹(V ∩ V'))[1]` into `Φ'(P⁻¹(V ∩ V'))[1]` under the
`F₁`-condition. -/
lemma shiftFiber_transition_mapsTo (c' : StrongBundleChart PX P)
    (h5 : ∀ x ∈ c.overlap c', x.2 ∈ range (c.F.toBase 1) →
      (c.transition c' x).2 ∈ range (c'.F.toBase 1)) :
    MapsTo (shiftFiber (c.transition c')) (strongShiftOne (c.overlap c'))
      (strongShiftOne (c'.overlap c)) := by
  intro p hp
  obtain ⟨y, ⟨hys, hys'⟩, hyp⟩ := hp
  have hr : (c' y).2 ∈ range (c'.F.toBase 1) := by
    have := h5 _ ⟨y, ⟨hys, hys'⟩, hyp⟩ ⟨p.2, rfl⟩
    rwa [← hyp, c.transition_apply c' hys] at this
  change ((shiftFiber (c.transition c') p).1, c'.F.toBase 1 (shiftFiber (c.transition c') p).2) ∈
    c'.overlap c
  rw [c.toBase_shiftFiber_transition c' hys hyp.symm hr]
  exact ⟨y, ⟨hys', hys⟩, rfl⟩

end Pieces

/-! ### Transition maps of compatible charts on pieces -/

section CompatiblePieces

variable {c c' : StrongBundleChart PX P}

/-- For compatible charts and an open `t ⊆ V ∩ V'`, `Φ' ∘ Φ⁻¹ : Φ(P⁻¹(t)) → Φ'(P⁻¹(t))` is
sc-smooth (`[0]`). -/
theorem Compatible.isScSmoothRetractMap_image_preimage (h : c.Compatible c') {t : Set X}
    (ht : t ⊆ c.φ.source ∩ c'.φ.source) (hto : IsOpen t) :
    IsScSmoothRetractMap (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ)
      (c.toPartialEquiv '' (P ⁻¹' t)) (c'.φ.model.E.prod c'.F) (c'.φ.model.C ×ˢ univ)
      (c'.toPartialEquiv '' (P ⁻¹' t)) (c.transition c') := by
  obtain ⟨W, -, hWeq⟩ := c.φ.exists_isOpen_image_eq (ht.trans inter_subset_left) hto
  rw [← c.overlap_inter_eq ht hWeq]
  refine (h.1.restrict (c.isScRetract_overlap' c')).mono_target ?_
  rw [c.overlap_inter_eq ht hWeq]
  exact c.transition_mapsTo_image_preimage c' ht

/-- For compatible charts and an open `t ⊆ V ∩ V'`,
`(Φ' ∘ Φ⁻¹)[1] : Φ(P⁻¹(t))[1] → Φ'(P⁻¹(t))[1]` is sc-smooth (`[1]`). -/
theorem Compatible.isScSmoothRetractMap_image_preimage_one (h : c.Compatible c') {t : Set X}
    (ht : t ⊆ c.φ.source ∩ c'.φ.source) (hto : IsOpen t) :
    IsScSmoothRetractMap (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
      (strongShiftOne (c.toPartialEquiv '' (P ⁻¹' t))) (c'.φ.model.E.prod c'.F.shift)
      (c'.φ.model.C ×ˢ univ) (strongShiftOne (c'.toPartialEquiv '' (P ⁻¹' t)))
      (shiftFiber (c.transition c')) := by
  obtain ⟨W, -, hWeq⟩ := c.φ.exists_isOpen_image_eq (ht.trans inter_subset_left) hto
  rw [← c.overlap_inter_eq ht hWeq, strongShiftOne_inter_prod]
  refine (h.2.2.1.restrict (c.isScRetract_overlap_one' c')).mono_target ?_
  rintro p ⟨hp, hpW⟩
  have hk : (p.1, c.F.toBase 1 p.2) ∈ c.toPartialEquiv '' (P ⁻¹' t) := by
    rw [← c.overlap_inter_eq ht hWeq]; exact ⟨hp, hpW.1, mem_univ _⟩
  obtain ⟨y, hy, hyk⟩ := hk
  have hys := c.mem_source_of_mem_base (ht hy).1
  have hr : (c' y).2 ∈ range (c'.F.toBase 1) := by
    have := h.2.2.2.2.1 _ hp ⟨p.2, rfl⟩
    rwa [← hyk, c.transition_apply c' hys] at this
  change ((shiftFiber (c.transition c') p).1, c'.F.toBase 1 (shiftFiber (c.transition c') p).2) ∈
    c'.toPartialEquiv '' (P ⁻¹' t)
  rw [c.toBase_shiftFiber_transition c' hys hyk.symm hr]
  exact ⟨y, hy, rfl⟩

end CompatiblePieces

/-! ### Locality of compatibility -/

/-- One direction of the locality of compatibility: the `[0]`-, `[1]`-transitions `c → c'` and the
`F₁`-condition `c → c'`. -/
private theorem compatible_of_locally_aux (S : Set (StrongBundleChart PX P))
    (c c' : StrongBundleChart PX P) (hc : ∀ χ ∈ S, c.Compatible χ)
    (hc' : ∀ χ ∈ S, χ.Compatible c')
    (hcover : ∀ y ∈ c.toPartialEquiv.source ∩ c'.toPartialEquiv.source,
      ∃ χ ∈ S, y ∈ χ.toPartialEquiv.source) :
    IsScSmoothRetractMap (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) (c.overlap c')
      (c'.φ.model.E.prod c'.F) (c'.φ.model.C ×ˢ univ) (c'.overlap c) (c.transition c') ∧
    IsScSmoothRetractMap (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
      (strongShiftOne (c.overlap c')) (c'.φ.model.E.prod c'.F.shift) (c'.φ.model.C ×ˢ univ)
      (strongShiftOne (c'.overlap c)) (shiftFiber (c.transition c')) ∧
    (∀ x ∈ c.overlap c', x.2 ∈ range (c.F.toBase 1) →
      (c.transition c' x).2 ∈ range (c'.F.toBase 1)) := by
  -- the `F₁`-condition, through a chart `χ` of `S` around the point
  have h5 : ∀ x ∈ c.overlap c', x.2 ∈ range (c.F.toBase 1) →
      (c.transition c' x).2 ∈ range (c'.F.toBase 1) := by
    rintro _ ⟨y, hy, rfl⟩ hx
    obtain ⟨χ, hχ, hyχ⟩ := hcover y hy
    have h1 := (hc χ hχ).2.2.2.2.1 (c y) ⟨y, ⟨hy.1, hyχ⟩, rfl⟩ hx
    rw [c.transition_apply χ hy.1] at h1
    have h2 := (hc' χ hχ).2.2.2.2.1 (χ y) ⟨y, ⟨hyχ, hy.2⟩, rfl⟩ h1
    rw [χ.transition_apply c' hyχ] at h2
    rw [c.transition_apply c' hy.1]
    exact h2
  -- the local data around `y ∈ P⁻¹(V ∩ V')`: a chart `χ ∈ S` and `t = V ∩ V' ∩ V_χ`
  have hloc : ∀ y ∈ c.toPartialEquiv.source ∩ c'.toPartialEquiv.source, ∃ χ ∈ S, ∃ t : Set X,
      IsOpen t ∧ P y ∈ t ∧ t ⊆ c.φ.source ∩ c'.φ.source ∧ t ⊆ c.φ.source ∩ χ.φ.source ∧
        t ⊆ χ.φ.source ∩ c'.φ.source := by
    intro y hy
    obtain ⟨χ, hχ, hyχ⟩ := hcover y hy
    refine ⟨χ, hχ, c.φ.source ∩ c'.φ.source ∩ χ.φ.source,
      (c.φ.isOpen_source.inter c'.φ.isOpen_source).inter χ.φ.isOpen_source,
      ⟨⟨c.mem_base_of_mem_source hy.1, c'.mem_base_of_mem_source hy.2⟩,
        χ.mem_base_of_mem_source hyχ⟩, inter_subset_left, fun x hx => ⟨hx.1.1, hx.2⟩,
      fun x hx => ⟨hx.2, hx.1.2⟩⟩
  have hsub : ∀ {t : Set X}, t ⊆ c.φ.source ∩ c'.φ.source →
      c'.toPartialEquiv '' (P ⁻¹' t) ⊆ c'.overlap c := fun {t} ht => by
    rw [c'.overlap_eq_image_preimage]
    exact image_mono (preimage_mono fun x hx => ⟨(ht hx).2, (ht hx).1⟩)
  refine ⟨?_, ?_, h5⟩
  · -- `[0]`: near `Φ(y)`, `Φ' ∘ Φ⁻¹ = (Φ' ∘ Φ_χ⁻¹) ∘ (Φ_χ ∘ Φ⁻¹)`
    refine IsScSmoothRetractMap.of_locally (c.transition_mapsTo c') ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨χ, hχ, t, hto, hyt, ht, htχ, htχ'⟩ := hloc y hy
    obtain ⟨W, hW, hWeq⟩ := c.φ.exists_isOpen_image_eq (ht.trans inter_subset_left) hto
    refine ⟨W ×ˢ univ, hW.prod isOpen_univ, ⟨?_, mem_univ _⟩, ?_⟩
    · have h1 : c.φ (P y) ∈ c.φ '' t := ⟨P y, hyt, rfl⟩
      rw [hWeq] at h1
      rw [c.covers y hy.1]; exact h1.2
    rw [c.overlap_inter_eq ht hWeq]
    have h1 := (hc χ hχ).isScSmoothRetractMap_image_preimage htχ hto
    have h2 := (hc' χ hχ).isScSmoothRetractMap_image_preimage htχ' hto
    have h3 := h2.comp h1 (χ.isScRetract_image_preimage (htχ'.trans inter_subset_left) hto)
    refine (h3.mono_target (h3.mapsTo.mono_right (hsub ht))).congr ?_
    rintro _ ⟨z, hz, rfl⟩
    have hzs := c.mem_source_of_mem_base (ht hz).1
    have hzχ := χ.mem_source_of_mem_base (htχ hz).2
    simp only [Function.comp_apply]
    rw [c.transition_apply χ hzs, χ.transition_apply c' hzχ, c.transition_apply c' hzs]
  · -- `[1]`: the same factorization on `K[1]`
    refine IsScSmoothRetractMap.of_locally (c.shiftFiber_transition_mapsTo c' h5) ?_
    intro p hp
    obtain ⟨y, hy, hyp⟩ := hp
    obtain ⟨χ, hχ, t, hto, hyt, ht, htχ, htχ'⟩ := hloc y hy
    obtain ⟨W, hW, hWeq⟩ := c.φ.exists_isOpen_image_eq (ht.trans inter_subset_left) hto
    refine ⟨W ×ˢ univ, hW.prod isOpen_univ, ⟨?_, mem_univ _⟩, ?_⟩
    · have h1 : c.φ (P y) ∈ c.φ '' t := ⟨P y, hyt, rfl⟩
      rw [hWeq] at h1
      have h2 : (c y).1 = p.1 := congrArg Prod.fst hyp
      rw [← h2, c.covers y hy.1]; exact h1.2
    rw [← strongShiftOne_inter_prod, c.overlap_inter_eq ht hWeq]
    have h1 := (hc χ hχ).isScSmoothRetractMap_image_preimage_one htχ hto
    have h2 := (hc' χ hχ).isScSmoothRetractMap_image_preimage_one htχ' hto
    have h3 := h2.comp h1 (χ.isScRetract_one_image_preimage (htχ'.trans inter_subset_left) hto)
    refine (h3.mono_target (h3.mapsTo.mono_right fun q hq => hsub ht hq)).congr ?_
    rintro q ⟨z, hz, hzq⟩
    have hzs := c.mem_source_of_mem_base (ht hz).1
    have hzχ := χ.mem_source_of_mem_base (htχ hz).2
    have hr : (χ z).2 ∈ range (χ.F.toBase 1) := by
      have := (hc χ hχ).2.2.2.2.1 (c z) ⟨z, ⟨hzs, hzχ⟩, rfl⟩ (by rw [hzq]; exact ⟨q.2, rfl⟩)
      rwa [c.transition_apply χ hzs] at this
    have e1 := c.toBase_shiftFiber_transition χ hzs hzq.symm hr
    simp only [Function.comp_apply]
    rw [χ.shiftFiber_transition_eq c' hzχ e1, c.shiftFiber_transition_eq c' hzs hzq.symm]

/-- **Compatibility of strong bundle charts is local** (the analogue of
`MChart.compatible_of_locally`): if `c` and `c'` are compatible with every chart of a family `S`
whose domains cover `P⁻¹(V ∩ V')`, then `c` and `c'` are compatible.  Near a point of
`Φ(P⁻¹(V ∩ V'))` the transitions factor through a chart `χ ∈ S`,
`Φ' ∘ Φ⁻¹ = (Φ' ∘ Φ_χ⁻¹) ∘ (Φ_χ ∘ Φ⁻¹)`, on `[0]` and on `[1]` (Theorem 2.1.15 (preprint 2.8) and the locality of
sc-smoothness, `IsScSmoothRetractMap.of_locally`); the `F₁`-condition passes through `χ`.  No
continuity of `P` is needed.  (Implicit in Definition 2.6.5 (preprint 2.51)'s "equivalence class"; round-trip
item V2.58.) -/
theorem compatible_of_locally (c c' : StrongBundleChart PX P) (S : Set (StrongBundleChart PX P))
    (hc : ∀ χ ∈ S, c.Compatible χ) (hc' : ∀ χ ∈ S, χ.Compatible c')
    (hcover : ∀ y ∈ c.toPartialEquiv.source ∩ c'.toPartialEquiv.source,
      ∃ χ ∈ S, y ∈ χ.toPartialEquiv.source) :
    c.Compatible c' := by
  obtain ⟨k1, k3, k5⟩ := compatible_of_locally_aux S c c' hc hc' hcover
  obtain ⟨k2, k4, k6⟩ := compatible_of_locally_aux S c' c (fun χ hχ => (hc' χ hχ).symm)
    (fun χ hχ => (hc χ hχ).symm) fun y hy => hcover y ⟨hy.2, hy.1⟩
  exact ⟨k1, k2, k3, k4, k5, k6⟩

/-! ### Restriction of a strong bundle chart -/

section Restrict

variable (c : StrongBundleChart PX P) {s : Set X} (hs : s ⊆ c.φ.source) (hso : IsOpen s)

/-- An open `W ⊆ E₀` with `φ(s) = O ∩ W` (chosen once and for all). -/
def restrictOpen : Set (c.φ.model.E 0) :=
  Classical.choose (c.φ.exists_isOpen_image_eq hs hso)

/-- The chosen `W` is open. -/
lemma isOpen_restrictOpen : IsOpen (c.restrictOpen hs hso) :=
  (Classical.choose_spec (c.φ.exists_isOpen_image_eq hs hso)).1

/-- `φ(s) = O ∩ W` for the chosen `W`. -/
lemma image_eq_restrictOpen : c.φ '' s = c.φ.model.O ∩ c.restrictOpen hs hso :=
  (Classical.choose_spec (c.φ.exists_isOpen_image_eq hs hso)).2

/-- The base retraction `r` restricted to `U ∩ r⁻¹(W)`, `φ(s) = O ∩ W`. -/
abbrev restrictBase : ScRetraction c.φ.model.E c.φ.model.C :=
  (c.isRetraction.baseRetraction c.relOpen).restrict (c.isOpen_restrictOpen hs hso)

/-- The restricted base retraction has retract `φ(s)`. -/
lemma restrictBase_retract : (c.restrictBase hs hso).retract = c.φ '' s := by
  rw [ScRetraction.restrict_retract, c.base_retract, c.image_eq_restrictOpen hs hso]

/-- The new `K`: `R((U ∩ r⁻¹(W)) ◁ F) = {(u, h) ∈ K | u ∈ φ(s)}`. -/
lemma mem_restrict_K_iff {p : c.φ.model.E 0 × c.F 0} :
    p ∈ c.R '' ((c.restrictBase hs hso).U ×ˢ univ) ↔ p ∈ c.K ∧ p.1 ∈ c.φ '' s := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨q, ⟨hq.1.1, mem_univ _⟩, rfl⟩, ?_⟩
    rw [← c.restrictBase_retract hs hso]
    have h1 := c.isRetraction.apply_fst hq.1.1 q.2
    rw [Prod.mk.eta] at h1
    rw [h1]
    exact (c.restrictBase hs hso).apply_mem_retract hq.1
  · rintro ⟨hK, hp⟩
    rw [← c.restrictBase_retract hs hso] at hp
    exact ⟨p, ⟨(c.restrictBase hs hso).retract_subset hp, mem_univ _⟩, c.R_eq_self_of_mem_K hK⟩

/-- The restricted bundle chart `Φ|P⁻¹(s)`. -/
def restrictPE : PartialEquiv Y (c.φ.model.E 0 × c.F 0) where
  toFun y := c y
  invFun p := c.toPartialEquiv.symm p
  source := P ⁻¹' s
  target := c.R '' ((c.restrictBase hs hso).U ×ˢ univ)
  map_source' y hy := by
    have hys := c.mem_source_of_mem_base (hs hy)
    refine (c.mem_restrict_K_iff hs hso).2 ⟨?_, ?_⟩
    · rw [← c.image_source]; exact ⟨y, hys, rfl⟩
    · rw [c.covers y hys]; exact ⟨P y, hy, rfl⟩
  map_target' p hp := by
    obtain ⟨hK, x, hx, hxp⟩ := (c.mem_restrict_K_iff hs hso).1 hp
    have hK' : p ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hK
    have hys := c.toPartialEquiv.map_target hK'
    have hPy := c.mem_base_of_mem_source hys
    have he : c.φ x = c.φ (P (c.toPartialEquiv.symm p)) := by
      rw [← c.covers _ hys, c.toPartialEquiv.right_inv hK', hxp]
    change P (c.toPartialEquiv.symm p) ∈ s
    rw [← c.φ.toPartialEquiv.injOn (hs hx) hPy he]; exact hx
  left_inv' y hy := c.toPartialEquiv.left_inv (c.mem_source_of_mem_base (hs hy))
  right_inv' p hp := by
    have hK' : p ∈ c.toPartialEquiv.target := by
      rw [c.target_eq]; exact ((c.mem_restrict_K_iff hs hso).1 hp).1
    exact c.toPartialEquiv.right_inv hK'

/-- **The restriction of a strong bundle chart** `(Φ, P⁻¹(V), K, U ◁ F)` to an open subset
`s ⊆ V` of the domain of its base chart (as `MChart.restrict` does for M-polyfold charts): the
strong bundle chart `(Φ|P⁻¹(s), P⁻¹(s), K_s, (U ∩ r⁻¹(W)) ◁ F)` over the base chart `φ|s`, with
`φ(s) = O ∩ W` and `K_s = {(u, h) ∈ K | u ∈ φ(s)}` (`restrict_K`).  Round-trip items V5.4 and
V2.58 (an auditor's construction, `RoundTrip/Items/V5_4.lean`, adapted from the re-centred
charts of `Polyfold/Chapter4/Recentre.lean`). -/
def restrict : StrongBundleChart PX P where
  φ := c.φ.restrict hs hso
  isChart := MPolyfold.IsChart.restrict PX c.isChart hs hso
  F := c.F
  U := (c.restrictBase hs hso).U
  R := c.R
  relOpen := (c.restrictBase hs hso).relOpen
  isRetraction := c.isRetraction.restrict c.relOpen (c.isOpen_restrictOpen hs hso)
  base_retract := c.restrictBase_retract hs hso
  toPartialEquiv := c.restrictPE hs hso
  source_eq := rfl
  target_eq := rfl
  continuousOn_toFun := c.continuousOn_toFun.mono fun y hy => c.mem_source_of_mem_base (hs hy)
  continuousOn_invFun := c.continuousOn_invFun.mono fun p hp => by
    rw [c.target_eq]; exact ((c.mem_restrict_K_iff hs hso).1 hp).1
  covers y hy := c.covers y (c.mem_source_of_mem_base (hs hy))
  fiber_linear x hx := c.fiber_linear x (hs hx)

/-- The base chart of the restriction is `φ|s`. -/
@[simp] lemma restrict_φ : (c.restrict hs hso).φ = c.φ.restrict hs hso := rfl

/-- The fibre model is unchanged. -/
@[simp] lemma restrict_F : (c.restrict hs hso).F = c.F := rfl

/-- The strong bundle retraction is unchanged (on a smaller domain). -/
@[simp] lemma restrict_R : (c.restrict hs hso).R = c.R := rfl

/-- `Φ|P⁻¹(s)` agrees with `Φ`. -/
@[simp] lemma restrict_apply (y : Y) : c.restrict hs hso y = c y := rfl

/-- The inverse of `Φ|P⁻¹(s)` agrees with `Φ⁻¹`. -/
@[simp] lemma restrict_symm_apply (p : c.φ.model.E 0 × c.F 0) :
    (c.restrict hs hso).toPartialEquiv.symm p = c.toPartialEquiv.symm p := rfl

/-- The domain of the restriction is `P⁻¹(s)`. -/
@[simp] lemma restrict_source : (c.restrict hs hso).toPartialEquiv.source = P ⁻¹' s := rfl

/-- The domain of the restricted base chart is `s`. -/
lemma restrict_φ_source : (c.restrict hs hso).φ.source = s := rfl

/-- `K_s = {(u, h) ∈ K | u ∈ φ(s)}`. -/
lemma restrict_K : (c.restrict hs hso).K = {p ∈ c.K | p.1 ∈ c.φ '' s} := by
  ext p; exact c.mem_restrict_K_iff hs hso

/-- The domain of the restricted retraction is `{u ∈ U | r(u) ∈ φ(s)}`; it does not depend on the
choice of `W` with `φ(s) = O ∩ W`. -/
lemma restrict_U :
    (c.restrict hs hso).U = {u ∈ c.U | IsStrongBundleMap.base c.R u ∈ c.φ '' s} := by
  ext u
  change u ∈ c.U ∧ IsStrongBundleMap.base c.R u ∈ c.restrictOpen hs hso ↔ _
  rw [c.image_eq_restrictOpen hs hso]
  constructor
  · rintro ⟨hu, hW⟩
    refine ⟨hu, ?_, hW⟩
    rw [← c.base_retract]
    exact (c.isRetraction.baseRetraction c.relOpen).apply_mem_retract hu
  · rintro ⟨hu, -, hW⟩
    exact ⟨hu, hW⟩

/-- The lift `Φ(y)[1]` is unchanged by restriction (so is `|·|₁`). -/
@[simp] lemma liftOne_restrict (y : Y) : (c.restrict hs hso).liftOne y = c.liftOne y := rfl

variable (c' : StrongBundleChart PX P)

/-- The overlap of the restricted chart with `c'`, seen in the restricted chart. -/
lemma restrict_overlap :
    (c.restrict hs hso).overlap c' = c.toPartialEquiv '' (P ⁻¹' (s ∩ c'.φ.source)) := by
  rw [StrongBundleChart.overlap, c'.source_eq, preimage_inter]; rfl

/-- The overlap of `c'` with the restricted chart, seen in `c'`. -/
lemma overlap_restrict :
    c'.overlap (c.restrict hs hso) = c'.toPartialEquiv '' (P ⁻¹' (s ∩ c'.φ.source)) := by
  rw [StrongBundleChart.overlap, c'.source_eq, inter_comm s, preimage_inter]; rfl

variable {c c'} in
/-- **Compatibility passes to the restriction of the first chart.** -/
theorem Compatible.restrict_left (h : c.Compatible c') : (c.restrict hs hso).Compatible c' := by
  have ht : s ∩ c'.φ.source ⊆ c.φ.source ∩ c'.φ.source := fun x hx => ⟨hs hx.1, hx.2⟩
  have ht' : s ∩ c'.φ.source ⊆ c'.φ.source ∩ c.φ.source := fun x hx => ⟨hx.2, hs hx.1⟩
  have hto : IsOpen (s ∩ c'.φ.source) := hso.inter c'.φ.isOpen_source
  have hsub : (c.restrict hs hso).overlap c' ⊆ c.overlap c' := by
    rw [c.restrict_overlap hs hso c', c.overlap_eq_image_preimage]
    exact image_mono (preimage_mono ht)
  have hsub' : c'.overlap (c.restrict hs hso) ⊆ c'.overlap c := by
    rw [c.overlap_restrict hs hso c', c'.overlap_eq_image_preimage]
    exact image_mono (preimage_mono ht')
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c.restrict_overlap hs hso c', c.overlap_restrict hs hso c']
    exact h.isScSmoothRetractMap_image_preimage ht hto
  · rw [c.restrict_overlap hs hso c', c.overlap_restrict hs hso c']
    exact h.symm.isScSmoothRetractMap_image_preimage ht' hto
  · rw [c.restrict_overlap hs hso c', c.overlap_restrict hs hso c']
    exact h.isScSmoothRetractMap_image_preimage_one ht hto
  · rw [c.restrict_overlap hs hso c', c.overlap_restrict hs hso c']
    exact h.symm.isScSmoothRetractMap_image_preimage_one ht' hto
  · intro x hx hx2
    exact h.2.2.2.2.1 x (hsub hx) hx2
  · intro x hx hx2
    exact h.2.2.2.2.2 x (hsub' hx) hx2

variable {c c'} in
/-- Compatibility passes to the restriction of the second chart. -/
theorem Compatible.restrict_right (h : c'.Compatible c) : c'.Compatible (c.restrict hs hso) :=
  (h.symm.restrict_left hs hso).symm

variable {c} in
/-- Compatibility passes to restrictions of both charts. -/
theorem Compatible.restrict {c' : StrongBundleChart PX P} (h : c.Compatible c') {t : Set X}
    (ht : t ⊆ c'.φ.source) (hto : IsOpen t) :
    (c.restrict hs hso).Compatible (c'.restrict ht hto) :=
  (h.restrict_left hs hso).restrict_right ht hto

end Restrict

end StrongBundleChart

/-! ### Equivalence of strong bundle atlases -/

namespace StrongBundleAtlas

/-- **Definition 2.6.4 (preprint 2.50)**: equivalence of strong bundle atlases ("their union is an atlas") is the
pairwise compatibility of their charts. -/
theorem equiv_iff (A B : StrongBundleAtlas PX P) :
    A.Equiv B ↔ ∀ c ∈ A.charts, ∀ c' ∈ B.charts, c.Compatible c' := by
  constructor
  · rintro ⟨D, hD⟩ c hc c' hc'
    exact D.compatible c (hD ▸ Or.inl hc) c' (hD ▸ Or.inr hc')
  · intro h
    refine ⟨⟨A.charts ∪ B.charts, ?_, fun y => ?_⟩, rfl⟩
    · rintro c (hc | hc) c' (hc' | hc')
      · exact A.compatible c hc c' hc'
      · exact h c hc c' hc'
      · exact (h c' hc' c hc).symm
      · exact B.compatible c hc c' hc'
    · obtain ⟨c, hc, hy⟩ := A.cover y
      exact ⟨c, Or.inl hc, hy⟩

/-- Equivalence of strong bundle atlases is reflexive. -/
lemma Equiv.refl (A : StrongBundleAtlas PX P) : A.Equiv A := ⟨A, (union_self _).symm⟩

/-- Equivalence of strong bundle atlases is symmetric. -/
lemma Equiv.symm {A B : StrongBundleAtlas PX P} (h : A.Equiv B) : B.Equiv A := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D, hD.trans (union_comm _ _)⟩

/-- **Equivalence of strong bundle atlases is transitive** (presupposed by Definition 2.6.5 (preprint 2.51)'s
"an equivalence class of strong bundle atlases"; round-trip item V2.58): a chart of `A` and a
chart of `C` are compatible because both are compatible with the charts of `B`, which cover `Y`
(`StrongBundleChart.compatible_of_locally`). -/
theorem Equiv.trans {A B C : StrongBundleAtlas PX P} (hAB : A.Equiv B) (hBC : B.Equiv C) :
    A.Equiv C := by
  rw [equiv_iff] at hAB hBC ⊢
  intro c hc c'' hc''
  exact StrongBundleChart.compatible_of_locally c c'' B.charts (fun χ hχ => hAB c hc χ hχ)
    (fun χ hχ => hBC χ hχ c'' hc'') fun y _ => B.cover y

/-- **Equivalence of strong bundle atlases is an equivalence relation** (Definitions 2.6.4–2.6.5 (preprint 2.50–2.51);
round-trip item V2.58 (a)), for every `P : Y → X` (no continuity needed). -/
theorem equivalence : Equivalence (StrongBundleAtlas.Equiv (PX := PX) (P := P)) :=
  ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

end StrongBundleAtlas

end Polyfold
