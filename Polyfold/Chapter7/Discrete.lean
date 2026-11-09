import Polyfold.Chapter3.ParamPerturbation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017 book), Part II, Chapter 7, §7.1:
infrastructure for **Lemma 7.1.11 (2017: 7.1)** and **Proposition 7.1.12 (2017: 7.4)** (p. 293 (2017 p. 230): finitely many morphisms, finite
isotropy) and for **Theorem 7.1.13 (2017: 7.1)** (p. 293 (2017 p. 231): the sc-smooth map `Γ : G × U → 𝐗`) *(Part II has no
2014 preprint; numbers and pages are those of the 2017 text)*.

# Discreteness, finiteness, and discrete M-polyfolds

## What the text uses

(Lemma 7.1.11 (2017: 7.1)) If `t : s⁻¹(cl_X(U(x'))) → X` is proper, only finitely many morphisms `ψ` have
`s(ψ) = x` and `t(ψ) ∈ U(x')`.  The proof argues by contradiction with a sequence of distinct
morphisms `ψ_n : s(ψ_n) → x` with `s(ψ_n) ∈ U(x')`: properness gives a convergent subsequence,
`t` is a local sc-diffeomorphism near the limit, and `t(ψ_n) = t(ψ_m) = x` forces `ψ_n = ψ_m`.
(Proposition 7.1.12 (2017: 7.4), "as a consequence") The isotropy group `G_x` is finite.  (Theorem 7.1.13 (2017: 7.1)) For the
finite group `G = G_x` and an open `U ∋ x`, "a sc-smooth map `Γ : G × U → 𝐗`"; the text names no
M-polyfold structure on `G × U`, and the proof (Appendix 7.5.1) builds `Γ` sheet by sheet,
`Γ(g, ·)` being an inverse of `s` near `g`.

## What is formalized

* **Discrete fibres**: `IsLocallyInjective.isDiscrete_preimage_singleton` (Mathlib's `IsDiscrete`),
  `IsLocallyInjective.isDiscrete_of_subset_preimage`,
  `IsLocalHomeomorph.isDiscrete_preimage_singleton`; `MPolyfold.IsLocalScDiffeo.isLocallyInjective`
  and `MPolyfold.IsLocalScDiffeo.isDiscrete_preimage_singleton` (local sc-diffeomorphisms).
* **Proper maps with discrete fibres have finite fibres**: `IsProperMap.finite_preimage_singleton`,
  `IsProperMap.finite_preimage_singleton_of_isLocallyInjective`.
* **Lemma 7.1.11 (2017: 7.1) and Proposition 7.1.12 (2017: 7.4), abstract forms** (maps `s, t : M → X`, no groupoid structure):
  `finite_setOf_mem_of_isProperMap_domRestrict` (`{ψ | s ψ ∈ K ∧ t ψ = x}` is finite when
  `t : s⁻¹(K) → X` is proper and `t` is locally injective), `finite_setOf_src_eq_tgt_eq`,
  `finite_setOf_src_eq_self_tgt_eq_self` and `finite_subtype_src_eq_self_tgt_eq_self` (finite
  isotropy under Definition 7.1.3 (2017: 7.3) (3)); for M-polyfolds, with `t` a local sc-diffeomorphism
  (Definition 7.1.3 (2017: 7.3) (1)), `MPolyfold.finite_setOf_mem_of_isLocalScDiffeo` and
  `MPolyfold.finite_isotropy_of_isLocalScDiffeo`.
* **Non-vacuity**: `isotropy_snd_witness` (`s = t = π₂ : G × X → X`, the trivial action of a finite
  discrete `G`, satisfies the hypotheses at every point, and the isotropy set has `|G|` elements),
  with `isLocallyInjective_snd_of_discrete` and `isProperMap_domRestrict_snd`.
* `MPolyfold.IsScSmoothOn.of_locally`: sc-smoothness on an open set is local.
* **A discrete space as an M-polyfold with `ℝ⁰` charts**: the instance
  `paracompactSpace_of_discreteTopology`, `discreteChart g : {g} → ℝ⁰`, `discreteChart_compatible`,
  `discretePolyfold`, `isChart_discreteChart`, `discretePolyfold_levelSet`,
  `discretePolyfold_smoothSet` (every point is smooth), `isScSmoothMap_discrete_iff` (a map into a
  discrete M-polyfold is sc-smooth if and only if it is continuous), `isScSmoothMap_const_discrete`.
* **`G × X` and its sheets** (with `MPolyfold.prod`): `isOpen_sheet`, `isScSmoothMap_sheet`
  (`x ↦ (g, x)`), `isScDiffeoOn_snd_sheet` (`π₂ : {g} × X → X` is an sc-diffeomorphism),
  `prod_discrete_mem_levelSet_iff`, `degIndex_prod_discrete` (`d_{G × X}(g, x) = d_X(x)`), and
  **sc-smoothness on `G × U` is sc-smoothness on each sheet**: `isScSmoothOn_prod_discrete_iff`,
  `isScSmoothOn_univ_prod_discrete_iff`, `isScSmoothMap_prod_discrete_iff`.

## Readings

* Properness is Mathlib's `IsProperMap` of `(s ⁻¹' K).domRestrict t` (plan decision P3, with
  Mathlib's `Set.domRestrict`; `Set.restrict` is deprecated).  The finiteness needs neither
  sequences nor metrizability: a fibre of a proper map is compact, a fibre of a locally injective
  map is discrete, and a compact discrete set is finite (`IsCompact.finite`).  This is the text's
  sequence argument without the sequences.
* Lemma 7.1.11 (2017: 7.1) is formalized in the form its proof treats (targets `t(ψ) = x`, sources in
  `cl_X(U(x'))`); the statement's form (sources `s(ψ) = x`, targets in `U(x')`) follows by the
  inverse map `ι`, which exchanges `s` and `t` and belongs to the groupoid structure
  (`EpGroupoid.lean`).  The condition on the sources is used only as `s(ψ) ∈ cl_X(U(x'))`.
* "The finite group `G`" is read with the discrete topology, and `G × U` as the open subset
  `G × U` of the product M-polyfold `G × X` (`MPolyfold.prod`, `discretePolyfold`).
  `isScSmoothOn_univ_prod_discrete_iff` shows this is the text's sheet-by-sheet reading: `Γ` is
  sc-smooth on `G × U` if and only if every `Γ(g, ·)` is sc-smooth on `U`.  The plan asks for a
  finite discrete type; the construction works for every discrete type (paracompact because
  metrizable; Mathlib has no such instance, hence `paracompactSpace_of_discreteTopology`).
* The charts `{g} → ℝ⁰` are pairwise compatible: their transition maps are the identity of the
  one-point space `ℝ⁰`, on `ℝ⁰` (same point) or on `∅` (distinct points).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### Discrete fibres -/

section Fibres

variable {M X : Type*} [TopologicalSpace M]

/-- **The fibres of a locally injective map are discrete.** -/
theorem IsLocallyInjective.isDiscrete_preimage_singleton {f : M → X} (hf : IsLocallyInjective f)
    (x : X) : IsDiscrete (f ⁻¹' {x}) := by
  refine isDiscrete_iff_forall_mem_exists_isOpen.2 fun y hy => ?_
  obtain ⟨U, hU, hyU, hinj⟩ := hf y
  refine ⟨U, hU, Subset.antisymm (fun z hz => hinj hz.1 hyU (hz.2.trans hy.symm)) ?_⟩
  rintro z rfl
  exact ⟨hyU, hy⟩

/-- A subset of a fibre of a locally injective map is discrete. -/
theorem IsLocallyInjective.isDiscrete_of_subset_preimage {f : M → X} (hf : IsLocallyInjective f)
    {s : Set M} {x : X} (hs : s ⊆ f ⁻¹' {x}) : IsDiscrete s :=
  (IsLocallyInjective.isDiscrete_preimage_singleton hf x).mono hs

/-- **The fibres of a local homeomorphism are discrete.** -/
theorem IsLocalHomeomorph.isDiscrete_preimage_singleton [TopologicalSpace X] {f : M → X}
    (hf : IsLocalHomeomorph f) (x : X) : IsDiscrete (f ⁻¹' {x}) :=
  IsLocallyInjective.isDiscrete_preimage_singleton hf.isLocallyInjective x

end Fibres

/-! ### Proper maps with discrete fibres -/

section Finite

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]

/-- **A proper map with discrete fibres has finite fibres**: the fibre is compact (the preimage of
a point) and discrete. -/
theorem IsProperMap.finite_preimage_singleton {f : M → X} (hf : IsProperMap f) {x : X}
    (hd : IsDiscrete (f ⁻¹' {x})) : (f ⁻¹' {x}).Finite :=
  (hf.isCompact_preimage isCompact_singleton).finite hd

/-- A proper locally injective map has finite fibres. -/
theorem IsProperMap.finite_preimage_singleton_of_isLocallyInjective {f : M → X}
    (hf : IsProperMap f) (hi : IsLocallyInjective f) (x : X) : (f ⁻¹' {x}).Finite :=
  IsProperMap.finite_preimage_singleton hf (IsLocallyInjective.isDiscrete_preimage_singleton hi x)

/-- **Lemma 7.1.11 (2017: 7.1), abstract form.**  Let `s, t : M → X` with `t` locally injective, and `K ⊆ X` such
that `t : s⁻¹(K) → X` is proper.  Then for every `x` only finitely many `ψ` have `s(ψ) ∈ K` and
`t(ψ) = x`. -/
theorem finite_setOf_mem_of_isProperMap_domRestrict {s t : M → X} (ht : IsLocallyInjective t)
    {K : Set X} (hK : IsProperMap ((s ⁻¹' K).domRestrict t)) (x : X) :
    {ψ | s ψ ∈ K ∧ t ψ = x}.Finite := by
  refine ((IsProperMap.finite_preimage_singleton_of_isLocallyInjective hK
    (ht.comp_right continuous_subtype_val Subtype.val_injective) x).image Subtype.val).subset ?_
  rintro ψ ⟨hψK, hψx⟩
  exact ⟨⟨ψ, hψK⟩, hψx, rfl⟩

/-- **Proposition 7.1.12 (2017: 7.4), abstract form** (with `y = x`): under the properness of `t` on `s⁻¹(cl V)`,
only finitely many `φ` have `s(φ) = y` and `t(φ) = x`, for every `y ∈ cl V`. -/
theorem finite_setOf_src_eq_tgt_eq {s t : M → X} (ht : IsLocallyInjective t) {V : Set X}
    (hV : IsProperMap ((s ⁻¹' closure V).domRestrict t)) {x y : X} (hy : y ∈ closure V) :
    {φ | s φ = y ∧ t φ = x}.Finite :=
  (finite_setOf_mem_of_isProperMap_domRestrict ht hV x).subset fun _ hφ => ⟨hφ.1 ▸ hy, hφ.2⟩

/-- **Finite isotropy, abstract form** (Proposition 7.1.12 (2017: 7.4)): if `t` is locally injective and some open
`V ∋ x` makes `t : s⁻¹(cl V) → X` proper (Definition 7.1.3 (2017: 7.3) (3)), then only finitely many `φ` have
`s(φ) = x = t(φ)`. -/
theorem finite_setOf_src_eq_self_tgt_eq_self {s t : M → X} (ht : IsLocallyInjective t) {x : X}
    (hx : ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsProperMap ((s ⁻¹' closure V).domRestrict t)) :
    {φ | s φ = x ∧ t φ = x}.Finite := by
  obtain ⟨V, -, hxV, hV⟩ := hx
  exact finite_setOf_src_eq_tgt_eq ht hV (subset_closure hxV)

/-- The same, as a finite type. -/
theorem finite_subtype_src_eq_self_tgt_eq_self {s t : M → X} (ht : IsLocallyInjective t) {x : X}
    (hx : ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsProperMap ((s ⁻¹' closure V).domRestrict t)) :
    Finite {φ // s φ = x ∧ t φ = x} :=
  (finite_setOf_src_eq_self_tgt_eq_self ht hx).to_subtype

end Finite

/-! ### Non-vacuity: the trivial action of a finite group -/

section Witness

variable {G X : Type*} [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace X]

/-- `π₂ : G × X → X` is locally injective for discrete `G` (injective on each sheet `{g} × X`). -/
theorem isLocallyInjective_snd_of_discrete : IsLocallyInjective (Prod.snd : G × X → X) := fun p =>
  ⟨{p.1} ×ˢ univ, (isOpen_discrete _).prod isOpen_univ, ⟨rfl, mem_univ _⟩,
    fun _ ha _ hb hab => Prod.ext (ha.1.trans hb.1.symm) hab⟩

variable [Finite G]

omit [DiscreteTopology G] in
/-- For finite `G` and `s = t = π₂ : G × X → X`, the map `t : s⁻¹(K) → X` is proper for every
closed `K`. -/
theorem isProperMap_domRestrict_snd {K : Set X} (hK : IsClosed K) :
    IsProperMap (((Prod.snd : G × X → X) ⁻¹' K).domRestrict Prod.snd) :=
  isProperMap_snd_of_compactSpace.restrict (hK.preimage continuous_snd)

/-- **The hypotheses of `finite_setOf_src_eq_self_tgt_eq_self` are satisfiable, with isotropy of
any finite size**: for `s = t = π₂ : G × X → X` (the trivial action of a finite discrete `G`) they
hold at every `x` (with `V = X`), and `{φ | s(φ) = x = t(φ)}` has `|G|` elements. -/
theorem isotropy_snd_witness (x : X) :
    IsLocallyInjective (Prod.snd : G × X → X) ∧ (∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      IsProperMap (((Prod.snd : G × X → X) ⁻¹' closure V).domRestrict Prod.snd)) ∧
    {φ : G × X | φ.2 = x ∧ φ.2 = x}.ncard = Nat.card G := by
  refine ⟨isLocallyInjective_snd_of_discrete,
    ⟨univ, isOpen_univ, mem_univ x, isProperMap_domRestrict_snd isClosed_closure⟩, ?_⟩
  have h : {φ : G × X | φ.2 = x ∧ φ.2 = x} = (fun g : G => (g, x)) '' univ := by
    ext φ
    constructor
    · rintro ⟨h, -⟩
      exact ⟨φ.1, mem_univ _, Prod.ext rfl h.symm⟩
    · rintro ⟨g, -, rfl⟩
      exact ⟨rfl, rfl⟩
  rw [h, ncard_image_of_injective _ fun a b hab => (Prod.ext_iff.1 hab).1, ncard_univ]

end Witness

/-! ### Local sc-diffeomorphisms are locally injective -/

namespace MPolyfold

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-- A local sc-diffeomorphism is locally injective (on a sheet `U` it has the left inverse `h`). -/
theorem IsLocalScDiffeo.isLocallyInjective {f : X → Z} (hf : P.IsLocalScDiffeo S f) :
    IsLocallyInjective f := fun x => by
  obtain ⟨U, V, h, hx, hd⟩ := hf x
  exact ⟨U, hd.isScSmoothOn.isOpen, hx, fun a ha b hb hab => by
    rw [← hd.left_inv a ha, hab, hd.left_inv b hb]⟩

/-- **The fibres of a local sc-diffeomorphism are discrete.** -/
theorem IsLocalScDiffeo.isDiscrete_preimage_singleton {f : X → Z} (hf : P.IsLocalScDiffeo S f)
    (z : Z) : IsDiscrete (f ⁻¹' {z}) :=
  Polyfold.IsLocallyInjective.isDiscrete_preimage_singleton hf.isLocallyInjective z

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- **Lemma 7.1.11 (2017: 7.1)** for M-polyfolds: `s, t : 𝐗 → X` with `t` a local sc-diffeomorphism and
`t : s⁻¹(K) → X` proper; then only finitely many `ψ` have `s(ψ) ∈ K` and `t(ψ) = x`. -/
theorem finite_setOf_mem_of_isLocalScDiffeo {s t : Y → X} (ht : Q.IsLocalScDiffeo P t)
    {K : Set X} (hK : IsProperMap ((s ⁻¹' K).domRestrict t)) (x : X) :
    {ψ | s ψ ∈ K ∧ t ψ = x}.Finite :=
  finite_setOf_mem_of_isProperMap_domRestrict ht.isLocallyInjective hK x

/-- **Proposition 7.1.12 (2017: 7.4)** for M-polyfolds, in the form Definition 7.1.3 (2017: 7.3) (1), (3) give it: if `t` is a
local sc-diffeomorphism and `t : s⁻¹(cl V(x)) → X` is proper for an open `V(x) ∋ x`, the
morphisms `φ` with `s(φ) = x = t(φ)` form a finite set. -/
theorem finite_isotropy_of_isLocalScDiffeo {s t : Y → X} (ht : Q.IsLocalScDiffeo P t) {x : X}
    (hx : ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsProperMap ((s ⁻¹' closure V).domRestrict t)) :
    {φ | s φ = x ∧ t φ = x}.Finite :=
  finite_setOf_src_eq_self_tgt_eq_self ht.isLocallyInjective hx

end MPolyfold

/-! ### Locality of sc-smoothness on open sets -/

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- **Sc-smoothness on an open set is local**: if every `x ∈ U` has an open neighbourhood
`U' ⊆ U` on which `f` is sc-smooth, then `f` is sc-smooth on `U`. -/
theorem IsScSmoothOn.of_locally {f : X → Y} {U : Set X} (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ U' : Set X, IsOpen U' ∧ x ∈ U' ∧ U' ⊆ U ∧ P.IsScSmoothOn Q f U') :
    P.IsScSmoothOn Q f U := by
  have hcont : ContinuousOn f U := fun x hx => by
    obtain ⟨U', hU', hxU', -, hf⟩ := h x hx
    exact (hf.continuousOn.continuousAt (hU'.mem_nhds hxU')).continuousWithinAt
  refine IsScSmoothOn.of_exists_charts hU hcont fun x hx => ?_
  obtain ⟨U', hU', hxU', hU'U, hf⟩ := h x hx
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f x)
  set V := (U' ∩ φ.source) ∩ f ⁻¹' ψ.source with hV
  have hVo : IsOpen V := (hf.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    (hU'.inter φ.isOpen_source) ψ.isOpen_source
  exact ⟨φ, ψ, V, hφ, hψ, hVo, ⟨⟨hxU', hxφ⟩, hfx⟩, fun y hy => ⟨hU'U hy.1.1, hy.1.2⟩,
    fun y hy => hy.2, hf.smooth φ ψ hφ hψ V hVo (fun y hy => hy.1) fun y hy => hy.2⟩

end MPolyfold

/-! ### A discrete space as an M-polyfold with `ℝ⁰` charts -/

section DiscretePolyfold

universe u v w

variable {G : Type u} [TopologicalSpace G] [DiscreteTopology G]

/-- A discrete space is paracompact (it is metrizable, `DiscreteTopology.metrizableSpace`). -/
instance (priority := 100) paracompactSpace_of_discreteTopology : ParacompactSpace G :=
  paracompactSpace_of_metrizableSpace G

/-- Any two points of `ℝ⁰` agree. -/
lemma rnModel_zero_eq (a b : (rnModel 0).E 0) : a = b :=
  Subsingleton.elim (α := Fin 0 → ℝ) a b

/-- **The chart `{g} → ℝ⁰`** of a discrete space at `g`: the constant map `0` on the open set
`{g}`, onto the retract `O = ℝ⁰` of the local model `(ℝ⁰, ℝ⁰, ℝ⁰)`. -/
def discreteChart (g : G) : MChart G where
  model := rnModel 0
  toPartialEquiv :=
    { toFun := fun _ => 0
      invFun := fun _ => g
      source := {g}
      target := univ
      map_source' := fun _ _ => mem_univ _
      map_target' := fun _ _ => rfl
      left_inv' := fun _ hx => hx.symm
      right_inv' := fun _ _ => rnModel_zero_eq _ _ }
  isOpen_source := isOpen_discrete _
  target_eq := rfl
  continuousOn_toFun := continuousOn_const
  continuousOn_invFun := continuousOn_const

@[simp] lemma discreteChart_source (g : G) : (discreteChart g).source = {g} := rfl

lemma mem_discreteChart_source (g : G) : g ∈ (discreteChart g).source := rfl

/-- Two charts `{g} → ℝ⁰`, `{g'} → ℝ⁰` are compatible: both transition maps are the identity of
`ℝ⁰`, on `ℝ⁰` if `g = g'` and on `∅` otherwise. -/
theorem discreteChart_compatible (g g' : G) : (discreteChart g).Compatible (discreteChart g') := by
  have hO : (discreteChart g).overlap (discreteChart g') =
      (discreteChart g').overlap (discreteChart g) := by
    change (fun _ => (0 : (rnModel 0).E 0)) '' ({g} ∩ {g'}) =
      (fun _ => (0 : (rnModel 0).E 0)) '' ({g'} ∩ {g})
    rw [inter_comm]
  have htr : ∀ a b : G, (discreteChart a).transition (discreteChart b) = id := fun _ _ =>
    funext fun _ => rnModel_zero_eq _ _
  refine ⟨?_, ?_⟩
  · rw [htr, ← hO]
    exact isScSmoothRetractMap_id _
  · rw [htr, hO]
    exact isScSmoothRetractMap_id _

variable (G) in
/-- **A discrete space as an M-polyfold**, with the charts `{g} → ℝ⁰` (`discreteChart`). -/
def discretePolyfold : MPolyfold G where
  atlas :=
    { charts := range discreteChart
      compatible := by
        rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩
        exact discreteChart_compatible g g'
      cover := fun g => ⟨discreteChart g, mem_range_self g, mem_discreteChart_source g⟩ }

theorem isChart_discreteChart (g : G) : (discretePolyfold G).IsChart (discreteChart g) :=
  (discretePolyfold G).isChart_of_mem (mem_range_self g)

/-- Every point of a discrete M-polyfold is on every level. -/
theorem discretePolyfold_levelSet (m : ℕ) : (discretePolyfold G).levelSet m = univ := by
  refine eq_univ_of_forall fun g => ?_
  rw [(discretePolyfold G).mem_levelSet_iff (isChart_discreteChart g) (mem_discreteChart_source g)]
  exact ⟨0, rnModel_zero_eq _ _⟩

/-- Every point of a discrete M-polyfold is smooth. -/
theorem discretePolyfold_smoothSet : (discretePolyfold G).smoothSet = univ := by
  refine eq_univ_of_forall fun g => mem_iInter.2 fun m => ?_
  rw [discretePolyfold_levelSet]
  exact mem_univ g

variable {X : Type v} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type w} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {PY : MPolyfold Y}

/-- **A continuous (that is, locally constant) map into a discrete M-polyfold is sc-smooth**: near
`x` it is constant, and its local representative is the constant map `0` into `ℝ⁰`. -/
theorem isScSmoothMap_discrete_of_continuous {f : X → G} (hf : Continuous f) :
    PX.IsScSmoothMap (discretePolyfold G) f := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ hf.continuousOn fun x _ => ?_
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source x
  set V := φ.source ∩ f ⁻¹' {f x} with hV
  have hVo : IsOpen V := φ.isOpen_source.inter ((isOpen_discrete _).preimage hf)
  refine ⟨φ, discreteChart (f x), V, hφ, isChart_discreteChart _, hVo, ⟨hx, rfl⟩,
    fun y hy => ⟨mem_univ y, hy.1⟩, fun y hy => hy.2, mapsTo_univ _ _, fun R _ => ?_⟩
  exact IsScSmooth.of_contDiffOn_finiteDimensional (V := Fin 0 → ℝ) R.isScDomain contDiffOn_const

/-- **Maps into a discrete M-polyfold**: sc-smooth if and only if continuous. -/
theorem isScSmoothMap_discrete_iff {f : X → G} :
    PX.IsScSmoothMap (discretePolyfold G) f ↔ Continuous f :=
  ⟨fun h => continuousOn_univ.1 h.continuousOn, isScSmoothMap_discrete_of_continuous⟩

/-- A constant map into a discrete M-polyfold is sc-smooth. -/
theorem isScSmoothMap_const_discrete (g : G) :
    PX.IsScSmoothMap (discretePolyfold G) fun _ => g :=
  isScSmoothMap_discrete_of_continuous continuous_const

/-! ### `G × X` and its sheets `{g} × X` -/

variable [ParacompactSpace (G × X)]

omit [T2Space X] [ParacompactSpace X] [ParacompactSpace (G × X)] in
/-- The sheet `{g} × X` is open in `G × X`. -/
theorem isOpen_sheet (g : G) : IsOpen ({g} ×ˢ univ : Set (G × X)) :=
  (isOpen_discrete _).prod isOpen_univ

/-- The sheet inclusion `x ↦ (g, x)` is sc-smooth. -/
theorem isScSmoothMap_sheet (g : G) :
    PX.IsScSmoothMap ((discretePolyfold G).prod PX) fun x => (g, x) :=
  MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete g) MPolyfold.isScSmoothMap_id

/-- **The projection `π₂ : {g} × X → X` is an sc-diffeomorphism**, with inverse `x ↦ (g, x)`. -/
theorem isScDiffeoOn_snd_sheet (g : G) :
    ((discretePolyfold G).prod PX).IsScDiffeoOn PX Prod.snd (fun x => (g, x)) ({g} ×ˢ univ)
      univ where
  isScSmoothOn := (MPolyfold.isScSmoothMap_snd _ _).mono (isOpen_sheet g) (subset_univ _)
  isScSmoothOn_inv := isScSmoothMap_sheet g
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := fun x _ => ⟨rfl, mem_univ x⟩
  left_inv := fun _ hp => Prod.ext hp.1.symm rfl
  right_inv := fun _ _ => rfl

/-- `(g, x)` is on level `m` of `G × X` if and only if `x` is on level `m` of `X`. -/
theorem prod_discrete_mem_levelSet_iff {m : ℕ} (p : G × X) :
    p ∈ ((discretePolyfold G).prod PX).levelSet m ↔ p.2 ∈ PX.levelSet m := by
  have hd := isScDiffeoOn_snd_sheet (PX := PX) p.1
  constructor
  · intro hp
    exact hd.isScSmoothOn.mapsTo_levelSet m ⟨⟨rfl, mem_univ _⟩, hp⟩
  · intro hp
    have := hd.isScSmoothOn_inv.mapsTo_levelSet m ⟨mem_univ _, hp⟩
    exact this

/-- `d_{G × X}(g, x) = d_X(x)` (Proposition 2.4.4 (preprint 2.24) along the sheet). -/
theorem degIndex_prod_discrete (p : G × X) :
    ((discretePolyfold G).prod PX).degIndex p = PX.degIndex p.2 :=
  proposition_2_4_4 (isScDiffeoOn_snd_sheet p.1) ⟨rfl, mem_univ _⟩

/-- **Sc-smoothness on `G × X` is sc-smoothness on each sheet**: for an open `W ⊆ G × X`, `f` is
sc-smooth on `W` if and only if every `f(g, ·)` is sc-smooth on `{x | (g, x) ∈ W}`. -/
theorem isScSmoothOn_prod_discrete_iff {f : G × X → Y} {W : Set (G × X)} (hW : IsOpen W) :
    ((discretePolyfold G).prod PX).IsScSmoothOn PY f W ↔
      ∀ g, PX.IsScSmoothOn PY (fun x => f (g, x)) {x | (g, x) ∈ W} := by
  constructor
  · intro hf g
    have hWg : IsOpen {x | (g, x) ∈ W} := hW.preimage (continuous_const.prodMk continuous_id)
    exact MPolyfold.IsScSmoothOn.comp hf ((isScSmoothMap_sheet g).mono hWg (subset_univ _))
      fun x hx => hx
  · intro h
    refine MPolyfold.IsScSmoothOn.of_locally hW fun p hp => ⟨W ∩ {p.1} ×ˢ univ,
      hW.inter (isOpen_sheet p.1), ⟨hp, rfl, mem_univ _⟩, inter_subset_left, ?_⟩
    have hsnd := (MPolyfold.isScSmoothMap_snd (discretePolyfold G) PX).mono
      (hW.inter (isOpen_sheet p.1)) (subset_univ _)
    have hsh : ∀ q ∈ W ∩ {p.1} ×ˢ (univ : Set X), (p.1, q.2) = q := fun q hq =>
      Prod.ext hq.2.1.symm rfl
    refine (MPolyfold.IsScSmoothOn.comp (h p.1) hsnd fun q hq => ?_).congr fun q hq => ?_
    · change (p.1, q.2) ∈ W
      rw [hsh q hq]
      exact hq.1
    · change f (p.1, q.2) = f q
      rw [hsh q hq]

/-- **Sc-smoothness on `G × U`**: `f` is sc-smooth on `G × U` (`U ⊆ X` open) if and only if every
`f(g, ·)` is sc-smooth on `U`. -/
theorem isScSmoothOn_univ_prod_discrete_iff {f : G × X → Y} {U : Set X} (hU : IsOpen U) :
    ((discretePolyfold G).prod PX).IsScSmoothOn PY f (univ ×ˢ U) ↔
      ∀ g, PX.IsScSmoothOn PY (fun x => f (g, x)) U := by
  rw [isScSmoothOn_prod_discrete_iff (isOpen_univ.prod hU)]
  have : ∀ g : G, {x | (g, x) ∈ (univ ×ˢ U : Set (G × X))} = U := fun g => by
    ext x
    simp
  simp only [this]

/-- **Sc-smooth maps on `G × X`**: `f` is sc-smooth if and only if every `f(g, ·)` is. -/
theorem isScSmoothMap_prod_discrete_iff {f : G × X → Y} :
    ((discretePolyfold G).prod PX).IsScSmoothMap PY f ↔
      ∀ g, PX.IsScSmoothMap PY fun x => f (g, x) :=
  isScSmoothOn_prod_discrete_iff isOpen_univ

end DiscretePolyfold

end Polyfold
