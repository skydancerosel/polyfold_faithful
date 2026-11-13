import Polyfold.Chapter1.Levels
import Polyfold.Chapter2.DegeneracyIndex

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.2, the
paragraph after Definition 2.3.8 (preprint 2.14): the shifted M-polyfold `X¹` (and, by iteration, `X_m`).

# The level `X¹` of an M-polyfold as an M-polyfold

## The text, paraphrased

"With this topology, the set `V_m := V ∩ X_m` is an open subset of `X_m` and `φ : V_m → O_m` is a
homeomorphism, so that the tuple `(V_m, φ, (O_m, C_m, E_m))` is a chart on `X_m`.  Any two such
charts are sc-smoothly compatible and the collection of such charts is an atlas on `X_m`."
(Theorem 2.3.10 (preprint 2.16)) `X_m` is metrizable, in particular paracompact (Appendix 2.6.2, with Smirnov's
theorem).

## What is formalized

* The level shift of the local data: `Polyfold.ScIso.shift`, `IsPartialQuadrant.shift` (`C¹ = C_1`
  is a partial quadrant in `E¹`), `IsRelOpenInQuadrant.shift`, `ScRetraction.shift` (the
  retraction `r : U¹ → U¹`, sc-smooth by Proposition 1.2.2 (preprint 1.17) = `IsScSmooth.shift`) with
  `ScRetraction.shift_retract : r(U¹) = O¹`, `IsScRetract.shift`, `LocalModel.shift`
  (`(O¹, C¹, E¹)`), and `IsScSmoothRetractMap.shift`: an sc-smooth map between retracts induces an
  sc-smooth map `f : O¹ → O'¹` (Proposition 1.2.2 (preprint 1.17) for retracts).
* Sc-smooth maps between retracts are continuous on every level
  (`IsScSmoothRetractMap.continuousOn_levelMap`, `mapsTo_levelMap`).
* `MPolyfold.Level P m`: the type `X_m` with the topology of Definition 2.3.8 (preprint 2.14)'s paragraph
  (`levelTopology`); `MPolyfold.continuous_levelVal` (the inclusion `X_m → X` is continuous) and
  the instance `T2Space (P.Level m)`.
* `MPolyfold.levelChart hφ x₀ : MChart (P.Level 1)`, the chart `(V₁, φ, (O₁, C₁, E¹))`;
  `MPolyfold.levelChart_compatible` ("any two such charts are sc-smoothly compatible");
  `MPolyfold.shift P : MPolyfold (P.Level 1)`, the M-polyfold `X¹`, with the instance argument
  `[ParacompactSpace (P.Level 1)]` (supplied by `MPolyfold.paracompactSpace_level` in
  `Metrizable.lean`); `MPolyfold.shift_isChart`.
* `MPolyfold.IsScSmoothOn.of_exists_charts`: Definition 2.3.8 (preprint 2.14) only needs to be checked for *one*
  pair of charts around each point (the locality of Definition 2.3.8 (preprint 2.14), used for `TX → X¹` and `Tf`).

## What the text leaves implicit, and the choices made

* `X_m` is treated for `m = 1` only; `X_m` is `(X¹)_{m-1}` by iteration (the level sets of `X¹`
  are those of `X` shifted by one, which is not formalized: gap G.6 of the report).
* Paracompactness of `X¹` (part of Theorem 2.3.10 (preprint 2.16)) is an instance argument
  `[ParacompactSpace (P.Level 1)]` of `MPolyfold.shift`, because this file comes before the
  metrizability proof.  It is not an added hypothesis: it is proved, for every `X_m` and with no
  added hypothesis, as the instance `MPolyfold.paracompactSpace_level` (Theorem 2.3.10 (preprint 2.16),
  `Polyfold.theorem_2_3_10`) in `Metrizable.lean`, so that wherever that file is imported the
  argument is filled in automatically.  The text's proof of paracompactness uses a locally finite
  closed refinement of a chart cover of `X` (Lemma 2.7.3 (preprint 2.56)), the paracompactness of closed subsets of
  the metrizable sets `V_m ≅ O_m`, and Proposition 2.7.4 (preprint 2.57) ("a regular space with a locally finite
  closed cover by paracompact subspaces is paracompact"), which also needs `X_m` to be *regular*,
  a point the text does not check (a Hausdorff locally metrizable space need not be regular; it
  holds here because `X_m → X` is continuous and `X` is regular).  The formal proof avoids Lemma
  2.56 and Proposition 2.7.4 (preprint 2.57) (not needed; formalized since in `GapP1_Michael.lean`, G.15): a partition of unity of `X`
  pulled back to `X_m` gives a metric (`Polyfold.metrizableSpace_of_pullback`, Smirnov's theorem),
  and paracompactness follows by Stone's theorem.
* The Hausdorff property of `X_m` is proved from the continuity and injectivity of the inclusion
  `X_m → X` (the text argues with disjoint neighbourhoods, which is the same).
* The inverse of a chart is a total function; `levelChart` therefore carries a junk value
  `x₀ : P.Level 1` (the type `X¹` may be empty).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E E' : ScBanach}

/-! ### Level shifts of the local data -/

/-- The level shift `T¹ : E¹ → F¹` of an sc-isomorphism. -/
def ScIso.shift {F : ScBanach} (T : ScIso E F) : ScIso E.shift F.shift where
  lvl m := T (m + 1)
  incl_comm m x := T.incl_comm (m + 1) x

/-- `C¹ = C ∩ E₁` is a partial quadrant in `E¹`. -/
theorem IsPartialQuadrant.shift {C : Set (E 0)} (hC : IsPartialQuadrant E C) :
    IsPartialQuadrant E.shift (E.lvlSet C 1) := by
  obtain ⟨n, W, T, rfl⟩ := hC
  refine ⟨n, W.shift, T.shift, ?_⟩
  rw [IsPartialQuadrant.lvlSet_eq T 1]
  rfl

/-- `U¹ = U ∩ E₁` is relatively open in the partial quadrant `C¹` of `E¹`. -/
theorem IsRelOpenInQuadrant.shift {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) :
    IsRelOpenInQuadrant E.shift (E.lvlSet C 1) (E.lvlSet U 1) := by
  obtain ⟨O, hO, rfl⟩ := hU.relOpen
  exact ⟨hU.isPartialQuadrant.shift, E.lvlSet O 1, E.isOpen_lvlSet hO 1, rfl⟩

/-- The sc-smooth retraction `r : U¹ → U¹` induced on level `1` (Proposition 1.2.2 (preprint 1.17)). -/
def ScRetraction.shift {C : Set (E 0)} (R : ScRetraction E C) :
    ScRetraction E.shift (E.lvlSet C 1) where
  U := E.lvlSet R.U 1
  toFun := levelMap R 1
  relOpen := R.relOpen.shift
  mapsTo x hx := R.isSc1.isSc0.levelMap_mapsTo R.mapsTo 1 hx
  isScSmooth := R.isScSmooth.shift R.isScDomain
  idem x hx := by
    apply E.toBase_injective 1
    have h1 : levelMap R 1 x ∈ E.lvlSet R.U 1 := R.isSc1.isSc0.levelMap_mapsTo R.mapsTo 1 hx
    rw [R.isSc1.isSc0.toBase_levelMap h1, R.isSc1.isSc0.toBase_levelMap hx]
    exact R.idem _ hx

lemma ScRetraction.shift_apply {C : Set (E 0)} (R : ScRetraction E C) (x : E 1) :
    R.shift x = levelMap R 1 x := rfl

lemma ScRetraction.shift_U {C : Set (E 0)} (R : ScRetraction E C) : R.shift.U = E.lvlSet R.U 1 := rfl

/-- `r(U¹) = O¹`. -/
theorem ScRetraction.shift_retract {C : Set (E 0)} (R : ScRetraction E C) :
    R.shift.retract = E.lvlSet R.retract 1 := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change E.toBase 1 (levelMap R 1 y) ∈ R.retract
    rw [R.isSc1.isSc0.toBase_levelMap hy]
    exact R.apply_mem_retract hy
  · intro hz
    have hzU : z ∈ E.lvlSet R.U 1 := R.lvlSet_retract_subset 1 hz
    refine ⟨z, hzU, ?_⟩
    exact R.levelMap_one_eq_self hz

theorem IsScRetract.shift {C O : Set (E 0)} (hO : IsScRetract E C O) :
    IsScRetract E.shift (E.lvlSet C 1) (E.lvlSet O 1) := by
  obtain ⟨R, rfl⟩ := hO
  exact ⟨R.shift, R.shift_retract⟩

/-- The local model `(O¹, C¹, E¹)`. -/
def LocalModel.shift (M : LocalModel) : LocalModel :=
  ⟨M.E.shift, M.E.lvlSet M.C 1, M.E.lvlSet M.O 1, M.isScRetract.shift⟩

@[simp] lemma LocalModel.shift_E (M : LocalModel) : M.shift.E = M.E.shift := rfl
@[simp] lemma LocalModel.shift_O (M : LocalModel) : M.shift.O = M.E.lvlSet M.O 1 := rfl
@[simp] lemma LocalModel.shift_C (M : LocalModel) : M.shift.C = M.E.lvlSet M.C 1 := rfl

section RetractMaps

variable {C : Set (E 0)} {C' : Set (E' 0)} {O : Set (E 0)} {O' : Set (E' 0)} {f : E 0 → E' 0}

/-- An sc-smooth map between retracts is sc⁰ on `O` (the text's "sc-smooth maps are in particular
sc⁰"). -/
theorem IsScSmoothRetractMap.isSc0 (hf : IsScSmoothRetractMap E C O E' C' O' f)
    (hO : IsScRetract E C O) : IsSc0 E E' O f := by
  obtain ⟨R, rfl⟩ := hO
  refine ((hf.comp_isScSmooth R rfl).isSc1.isSc0.mono R.retract_subset).congr fun x hx => ?_
  simp only [Function.comp_apply, R.apply_eq_self_of_mem_retract hx]

/-- An sc-smooth map between retracts maps `O_m` into `O'_m`, as level maps. -/
theorem IsScSmoothRetractMap.mapsTo_levelMap (hf : IsScSmoothRetractMap E C O E' C' O' f)
    (hO : IsScRetract E C O) (m : ℕ) : MapsTo (levelMap f m) (E.lvlSet O m) (E'.lvlSet O' m) :=
  (hf.isSc0 hO).levelMap_mapsTo hf.mapsTo m

/-- An sc-smooth map between retracts is continuous on every level `O_m → O'_m`. -/
theorem IsScSmoothRetractMap.continuousOn_levelMap (hf : IsScSmoothRetractMap E C O E' C' O' f)
    (hO : IsScRetract E C O) (m : ℕ) : ContinuousOn (levelMap f m) (E.lvlSet O m) :=
  (hf.isSc0 hO).continuousOn m

/-- **Proposition 1.2.2 (preprint 1.17) for retracts**: an sc-smooth map `f : (O, C, E) → (O', C', E')` induces an
sc-smooth map `f : (O¹, C¹, E¹) → (O'¹, C'¹, E'¹)` (its level-`1` map). -/
theorem IsScSmoothRetractMap.shift (hf : IsScSmoothRetractMap E C O E' C' O' f)
    (hO : IsScRetract E C O) :
    IsScSmoothRetractMap E.shift (E.lvlSet C 1) (E.lvlSet O 1) E'.shift (E'.lvlSet C' 1)
      (E'.lvlSet O' 1) (levelMap f 1) := by
  rw [isScSmoothRetractMap_iff_exists hO.shift]
  refine ⟨hf.mapsTo_levelMap hO 1, ?_⟩
  have hf0 := hf.isSc0 hO
  obtain ⟨R, rfl⟩ := hO
  refine ⟨R.shift, R.shift_retract, ?_⟩
  have h1 := (hf.comp_isScSmooth R rfl).shift R.isScDomain
  refine h1.congr R.shift.isScDomain fun x hx => ?_
  exact hf0.levelMap_comp R.isSc1.isSc0 R.mapsTo_retract hx

end RetractMaps

/-! ### The locality of Definition 2.3.8 (preprint 2.14) -/

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- **The locality of Definition 2.3.8 (preprint 2.14)**: `f : X → Y` is sc-smooth on the open set `U` as soon as it
is continuous on `U` and every `x ∈ U` has charts `φ` of `X` around `x`, `ψ` of `Y` around `f(x)`
and an open `V ∋ x`, `V ⊆ U ∩ dom φ`, `f(V) ⊆ dom ψ`, with `ψ ∘ f ∘ φ⁻¹` sc-smooth on `φ(V)`.
(The text's "the definition does not depend on the choice of sc-smoothly compatible charts".) -/
theorem IsScSmoothOn.of_exists_charts {f : X → Y} {U : Set X} (hU : IsOpen U)
    (hf : ContinuousOn f U)
    (h : ∀ x ∈ U, ∃ (φ : MChart X) (ψ : MChart Y) (V : Set X), P.IsChart φ ∧ Q.IsChart ψ ∧
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∩ φ.source ∧ MapsTo f V ψ.source ∧
      IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V) ψ.model.E ψ.model.C ψ.model.O
        (ψ ∘ f ∘ φ.symm)) :
    P.IsScSmoothOn Q f U where
  isOpen := hU
  continuousOn := hf
  smooth φ' ψ' hφ' hψ' V' hV' hV'U hfV' := by
    have hV'φ : V' ⊆ φ'.source := fun x hx => (hV'U hx).2
    refine IsScSmoothRetractMap.of_locally ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      change ψ' (f (φ'.symm (φ' x))) ∈ ψ'.model.O
      rw [φ'.symm_apply_apply (hV'φ hx)]
      exact ψ'.mapsTo_model _ (hfV' hx)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨φ, ψ, V, hφ, hψ, hVo, hxV, hVU, hfV, hsm⟩ := h x (hV'U hx).1
    -- the open set `V₀ = V ∩ V'`
    set V₀ := V ∩ V' with hV₀
    have hV₀o : IsOpen V₀ := hVo.inter hV'
    have hV₀φ' : V₀ ⊆ φ'.source := fun y hy => hV'φ hy.2
    have hV₀φ : V₀ ⊆ φ.source := fun y hy => (hVU hy.1).2
    obtain ⟨W, hW, hWeq⟩ := φ'.exists_isOpen_image_eq hV₀φ' hV₀o
    refine ⟨W, hW, ?_, ?_⟩
    · have : φ' x ∈ φ' '' V₀ := ⟨x, ⟨hxV, hx⟩, rfl⟩
      rw [hWeq] at this; exact this.2
    have hover : φ' '' V' ∩ W = φ' '' V₀ := by
      rw [hWeq]
      exact inter_eq_inter_of_subset (φ'.image_subset_model hV'φ)
        (hWeq ▸ image_mono inter_subset_right)
    rw [hover]
    -- `ψ' ∘ f ∘ φ'⁻¹ = (ψ' ∘ ψ⁻¹) ∘ (ψ ∘ f ∘ φ⁻¹) ∘ (φ ∘ φ'⁻¹)` on `φ'(V₀)`
    have h1 : IsScSmoothRetractMap φ'.model.E φ'.model.C (φ' '' V₀) φ.model.E φ.model.C (φ '' V₀)
        (φ'.transition φ) := by
      obtain ⟨W', hW', hW'eq⟩ := φ'.exists_isOpen_image_eq hV₀φ' hV₀o
      have := (hφ'.compatible hφ (P := P)).1.restrict (φ'.isScRetract_overlap φ) (W := W')
      have hover' : φ'.overlap φ ∩ W' = φ' '' V₀ := by
        rw [hW'eq]
        exact inter_eq_inter_of_subset (φ'.overlap_subset φ)
          (hW'eq ▸ image_mono fun y hy => ⟨hV₀φ' hy, hV₀φ hy⟩)
      rw [hover'] at this
      refine this.mono_target ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [φ'.transition_apply φ (hV₀φ' hy)]
      exact ⟨y, hy, rfl⟩
    have h2 : IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V₀) ψ.model.E ψ.model.C
        (ψ.overlap ψ') (ψ ∘ f ∘ φ.symm) := by
      obtain ⟨W', hW', hW'eq⟩ := φ.exists_isOpen_image_eq hV₀φ hV₀o
      have := hsm.restrict (φ.isScRetract_image (fun y hy => (hVU hy).2) hVo) (W := W')
      have hover' : φ '' V ∩ W' = φ '' V₀ := by
        rw [hW'eq]
        exact inter_eq_inter_of_subset (φ.image_subset_model fun y hy => (hVU hy).2)
          (hW'eq ▸ image_mono inter_subset_left)
      rw [hover'] at this
      refine this.mono_target ?_
      rintro _ ⟨y, hy, rfl⟩
      change ψ (f (φ.symm (φ y))) ∈ ψ.overlap ψ'
      rw [φ.symm_apply_apply (hV₀φ hy)]
      exact ⟨f y, ⟨hfV hy.1, hfV' hy.2⟩, rfl⟩
    have h3 : IsScSmoothRetractMap ψ.model.E ψ.model.C (ψ.overlap ψ') ψ'.model.E ψ'.model.C
        ψ'.model.O (ψ.transition ψ') :=
      (hψ.compatible hψ' (P := Q)).1.mono_target fun _ hz => (ψ'.overlap_subset ψ)
        (ψ.transition_mapsTo ψ' hz)
    have hφV₀ : IsScRetract φ.model.E φ.model.C (φ '' V₀) := φ.isScRetract_image hV₀φ hV₀o
    refine ((h3.comp h2 (ψ.isScRetract_overlap ψ')).comp h1 hφV₀).congr ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, φ'.transition_apply φ (hV₀φ' hy), φ'.symm_apply_apply (hV₀φ' hy),
      φ.symm_apply_apply (hV₀φ hy), ψ.transition_apply ψ' (hfV hy.1)]

/-! ### The topological space `X_m` -/

variable (P) in
/-- The level `X_m` of the M-polyfold `X`, as a type with the topology generated by the sets
`φ⁻¹(W)`, `W` open in `O_m` (the paragraph after Definition 2.3.8 (preprint 2.14)). -/
def Level (m : ℕ) : Type u := P.levelSet m

instance (m : ℕ) : TopologicalSpace (P.Level m) := P.levelTopology m

variable (P) in
/-- The inclusion `X_m → X`. -/
def levelVal (m : ℕ) (x : P.Level m) : X := (x : P.levelSet m).1

lemma levelVal_mem {m : ℕ} (x : P.Level m) : P.levelVal m x ∈ P.levelSet m := (x : P.levelSet m).2

variable (P) in
/-- A point of `X_m` as an element of `P.Level m`. -/
def levelMk (m : ℕ) (x : X) (hx : x ∈ P.levelSet m) : P.Level m := (⟨x, hx⟩ : P.levelSet m)

@[simp] lemma levelVal_levelMk (m : ℕ) (x : X) (hx : x ∈ P.levelSet m) :
    P.levelVal m (P.levelMk m x hx) = x := rfl

lemma levelVal_injective (m : ℕ) : Injective (P.levelVal m) := fun _ _ h => Subtype.ext h

lemma level_ext {m : ℕ} {x y : P.Level m} (h : P.levelVal m x = P.levelVal m y) : x = y :=
  levelVal_injective m h

/-- The generating sets of the topology on `X_m`, as sets of `P.Level m`. -/
lemma isOpen_level_basic {m : ℕ} {φ : MChart X} (hφ : P.IsChart φ) {W : Set (φ.model.E m)}
    (hW : IsOpen W) :
    IsOpen {x : P.Level m | P.levelVal m x ∈ φ.source ∧ levelLift φ m (P.levelVal m x) ∈ W} :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨φ, hφ, W, hW, rfl⟩

/-- `V_m = V ∩ X_m` is open in `X_m` for `V` open in `X`: the inclusion `X_m → X` is continuous. -/
theorem continuous_levelVal (m : ℕ) : Continuous (P.levelVal m) := by
  rw [continuous_def]
  intro V hV
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source (P.levelVal m x)
  -- `φ(V ∩ dom φ) = O ∩ W`; the preimage is the basic set of `W_m`
  obtain ⟨W, hW, hWeq⟩ := φ.exists_isOpen_image_eq (s := V ∩ φ.source) inter_subset_right
    (hV.inter φ.isOpen_source)
  refine ⟨{y : P.Level m | P.levelVal m y ∈ φ.source ∧
    levelLift φ m (P.levelVal m y) ∈ φ.model.E.lvlSet W m}, ?_, isOpen_level_basic hφ
    (φ.model.E.isOpen_lvlSet hW m), ?_⟩
  · rintro y ⟨hyφ, hyW⟩
    have h1 : φ (P.levelVal m y) ∈ φ.model.O ∩ W := by
      refine ⟨φ.mapsTo_model _ hyφ, ?_⟩
      have := hyW
      rwa [ScBanach.mem_lvlSet, P.toBase_levelLift hφ hyφ (levelVal_mem y)] at this
    rw [← hWeq] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    have : z = P.levelVal m y := φ.toPartialEquiv.injOn hz.2 hyφ hzeq
    rw [mem_preimage, ← this]; exact hz.1
  · refine ⟨hxφ, ?_⟩
    rw [ScBanach.mem_lvlSet, P.toBase_levelLift hφ hxφ (levelVal_mem x)]
    have : φ (P.levelVal m x) ∈ φ '' (V ∩ φ.source) := ⟨_, ⟨hx, hxφ⟩, rfl⟩
    rw [hWeq] at this
    exact this.2

/-- `X_m` is Hausdorff (the text: disjoint neighbourhoods in `X` give disjoint neighbourhoods in
`X_m`). -/
instance (m : ℕ) : T2Space (P.Level m) :=
  T2Space.of_injective_continuous (levelVal_injective m) (continuous_levelVal m)

/-! ### The charts `(V₁, φ, (O₁, C₁, E¹))` of `X¹` -/

section LevelChart

variable {φ ψ : MChart X}

open scoped Classical in
/-- The inverse `O₁ → V₁` of the level chart, `z ↦ φ⁻¹(z)`, with the junk value `x₀` off `O₁`. -/
def levelChartInv (hφ : P.IsChart φ) (x₀ : P.Level 1) (z : φ.model.E 1) : P.Level 1 :=
  if h : φ.model.E.toBase 1 z ∈ φ.model.O then
    P.levelMk 1 (φ.symm (φ.model.E.toBase 1 z)) ((P.mem_levelSet_iff hφ (φ.symm_mapsTo h)).2
      (by rw [φ.apply_symm_apply h]; exact ⟨z, rfl⟩))
  else x₀

lemma levelVal_levelChartInv (hφ : P.IsChart φ) (x₀ : P.Level 1) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z ∈ φ.model.O) :
    P.levelVal 1 (levelChartInv hφ x₀ z) = φ.symm (φ.model.E.toBase 1 z) := by
  unfold levelChartInv; rw [dif_pos hz]; rfl

/-- The chart `(V₁, φ, (O₁, C₁, E¹))` of `X¹` induced by the chart `φ` of `X`, with the junk value
`x₀` for the inverse outside `O₁`. -/
def levelChart (hφ : P.IsChart φ) (x₀ : P.Level 1) : MChart (P.Level 1) where
  model := φ.model.shift
  toPartialEquiv :=
    { toFun := fun x => levelLift φ 1 (P.levelVal 1 x)
      invFun := levelChartInv hφ x₀
      source := {x | P.levelVal 1 x ∈ φ.source}
      target := φ.model.E.lvlSet φ.model.O 1
      map_source' := fun x hx => by
        change φ.model.E.toBase 1 (levelLift φ 1 (P.levelVal 1 x)) ∈ φ.model.O
        rw [P.toBase_levelLift hφ hx (levelVal_mem x)]
        exact φ.mapsTo_model _ hx
      map_target' := fun z hz => by
        change P.levelVal 1 (levelChartInv hφ x₀ z) ∈ φ.source
        rw [levelVal_levelChartInv hφ x₀ hz]
        exact φ.symm_mapsTo hz
      left_inv' := fun x hx => by
        have h1 : φ.model.E.toBase 1 (levelLift φ 1 (P.levelVal 1 x)) ∈ φ.model.O := by
          rw [P.toBase_levelLift hφ hx (levelVal_mem x)]; exact φ.mapsTo_model _ hx
        apply level_ext
        rw [levelVal_levelChartInv hφ x₀ h1, P.toBase_levelLift hφ hx (levelVal_mem x),
          φ.symm_apply_apply hx]
      right_inv' := fun z hz => by
        change levelLift φ 1 (P.levelVal 1 (levelChartInv hφ x₀ z)) = z
        rw [levelVal_levelChartInv hφ x₀ hz]
        apply φ.model.E.toBase_injective 1
        have hmem : φ.symm (φ.model.E.toBase 1 z) ∈ P.levelSet 1 :=
          (P.mem_levelSet_iff hφ (φ.symm_mapsTo hz)).2 (by rw [φ.apply_symm_apply hz]; exact ⟨z, rfl⟩)
        rw [P.toBase_levelLift hφ (φ.symm_mapsTo hz) hmem]
        exact φ.apply_symm_apply hz }
  isOpen_source := by
    have := isOpen_level_basic (m := 1) hφ (W := univ) isOpen_univ
    simpa using this
  target_eq := rfl
  continuousOn_toFun := by
    rw [continuousOn_iff']
    intro W hW
    refine ⟨{x : P.Level 1 | P.levelVal 1 x ∈ φ.source ∧ levelLift φ 1 (P.levelVal 1 x) ∈ W},
      isOpen_level_basic hφ hW, ?_⟩
    ext x
    exact ⟨fun h => ⟨⟨h.2, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨ψ, hψ, W, hW, rfl⟩
    -- the preimage is `{z ∈ O₁ | ι z ∈ φ(V ∩ V') ∧ (ψ ∘ φ⁻¹)₁ z ∈ W}`
    obtain ⟨W₀, hW₀, hW₀eq⟩ := φ.exists_isOpen_image_eq (s := φ.source ∩ ψ.source) inter_subset_left
      (φ.isOpen_source.inter ψ.isOpen_source)
    have hcont : ContinuousOn (levelMap (φ.transition ψ) 1) (φ.model.E.lvlSet (φ.overlap ψ) 1) :=
      (hφ.compatible hψ (P := P)).1.continuousOn_levelMap (φ.isScRetract_overlap ψ) 1
    obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hcont) W hW
    have hov : φ.overlap ψ = φ.model.O ∩ W₀ := hW₀eq
    refine isOpen_induced_iff.2 ⟨φ.model.E.lvlSet W₀ 1 ∩ u,
      (φ.model.E.isOpen_lvlSet hW₀ 1).inter hu, ?_⟩
    ext ⟨z, hz⟩
    rw [iff_comm]
    have hzO : φ.model.E.toBase 1 z ∈ φ.model.O := hz
    change (P.levelVal 1 (levelChartInv hφ x₀ z) ∈ ψ.source ∧
      levelLift ψ 1 (P.levelVal 1 (levelChartInv hφ x₀ z)) ∈ W) ↔ _
    rw [levelVal_levelChartInv hφ x₀ hzO]
    have hz1 : φ.model.E.toBase 1 z ∈ φ.overlap ψ ↔ φ.symm (φ.model.E.toBase 1 z) ∈ ψ.source := by
      constructor
      · rintro ⟨y, hy, hyeq⟩
        rw [← hyeq, φ.symm_apply_apply hy.1]; exact hy.2
      · intro h
        exact ⟨_, ⟨φ.symm_mapsTo hzO, h⟩, φ.apply_symm_apply hzO⟩
    have hz2 : levelLift ψ 1 (φ.symm (φ.model.E.toBase 1 z)) = levelMap (φ.transition ψ) 1 z := rfl
    rw [hz2]
    constructor
    · rintro ⟨h1, h2⟩
      have hzov : z ∈ φ.model.E.lvlSet (φ.overlap ψ) 1 := hz1.2 h1
      have : z ∈ levelMap (φ.transition ψ) 1 ⁻¹' W ∩ φ.model.E.lvlSet (φ.overlap ψ) 1 := ⟨h2, hzov⟩
      rw [hueq] at this
      refine ⟨?_, this.1⟩
      have h3 : φ.model.E.toBase 1 z ∈ φ.model.O ∩ W₀ := hov ▸ hzov
      exact h3.2
    · rintro ⟨h1, h2⟩
      have hzov : z ∈ φ.model.E.lvlSet (φ.overlap ψ) 1 := by
        change φ.model.E.toBase 1 z ∈ φ.overlap ψ
        rw [hov]; exact ⟨hzO, h1⟩
      refine ⟨hz1.1 hzov, ?_⟩
      have : z ∈ u ∩ φ.model.E.lvlSet (φ.overlap ψ) 1 := ⟨h2, hzov⟩
      rw [← hueq] at this
      exact this.1

variable (hφ : P.IsChart φ) (x₀ : P.Level 1)

lemma levelChart_source : (levelChart hφ x₀).source = {x | P.levelVal 1 x ∈ φ.source} := rfl

lemma levelChart_apply (x : P.Level 1) : levelChart hφ x₀ x = levelLift φ 1 (P.levelVal 1 x) := rfl

lemma levelChart_model : (levelChart hφ x₀).model = φ.model.shift := rfl

lemma levelChart_symm_apply {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z ∈ φ.model.O) :
    P.levelVal 1 ((levelChart hφ x₀).symm z) = φ.symm (φ.model.E.toBase 1 z) :=
  levelVal_levelChartInv hφ x₀ hz

/-- The overlap of two level charts is the level-`1` part of the overlap of the charts. -/
lemma levelChart_overlap (hψ : P.IsChart ψ) (y₀ : P.Level 1) :
    (levelChart hφ x₀).overlap (levelChart hψ y₀) = φ.model.E.lvlSet (φ.overlap ψ) 1 := by
  ext z
  constructor
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    change φ.model.E.toBase 1 (levelLift φ 1 (P.levelVal 1 x)) ∈ φ.overlap ψ
    rw [P.toBase_levelLift hφ hx (levelVal_mem x)]
    exact ⟨_, ⟨hx, hx'⟩, rfl⟩
  · rintro ⟨x, hx, hxeq⟩
    have hx1 : x ∈ P.levelSet 1 := (P.mem_levelSet_iff hφ hx.1).2 ⟨z, hxeq.symm⟩
    refine ⟨P.levelMk 1 x hx1, ⟨hx.1, hx.2⟩, ?_⟩
    change levelLift φ 1 x = z
    apply φ.model.E.toBase_injective 1
    rw [P.toBase_levelLift hφ hx.1 hx1, hxeq]

/-- The transition map of two level charts is the level-`1` map of the transition map. -/
lemma levelChart_transition (hψ : P.IsChart ψ) (y₀ : P.Level 1) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z ∈ φ.model.O) :
    (levelChart hφ x₀).transition (levelChart hψ y₀) z = levelMap (φ.transition ψ) 1 z := by
  change levelLift ψ 1 (P.levelVal 1 ((levelChart hφ x₀).symm z)) = _
  rw [levelChart_symm_apply hφ x₀ hz]
  rfl

/-- "Any two such charts are sc-smoothly compatible": the level charts of two charts of the
structure are compatible (Proposition 1.2.2 (preprint 1.17) for the transition maps). -/
theorem levelChart_compatible (hψ : P.IsChart ψ) (y₀ : P.Level 1) :
    (levelChart hφ x₀).Compatible (levelChart hψ y₀) := by
  have key : ∀ (φ ψ : MChart X) (hφ : P.IsChart φ) (hψ : P.IsChart ψ) (x₀ y₀ : P.Level 1),
      IsScSmoothRetractMap (levelChart hφ x₀).model.E (levelChart hφ x₀).model.C
        ((levelChart hφ x₀).overlap (levelChart hψ y₀)) (levelChart hψ y₀).model.E
        (levelChart hψ y₀).model.C ((levelChart hψ y₀).overlap (levelChart hφ x₀))
        ((levelChart hφ x₀).transition (levelChart hψ y₀)) := by
    intro φ ψ hφ hψ x₀ y₀
    rw [levelChart_overlap, levelChart_overlap]
    have := (hφ.compatible hψ (P := P)).1.shift (φ.isScRetract_overlap ψ)
    refine this.congr fun z hz => ?_
    have hz' : φ.model.E.toBase 1 z ∈ φ.model.O := φ.overlap_subset ψ hz
    exact (levelChart_transition hφ x₀ hψ y₀ hz').symm
  exact ⟨key φ ψ hφ hψ x₀ y₀, key ψ φ hψ hφ y₀ x₀⟩

end LevelChart

/-! ### The M-polyfold `X¹` -/

variable (P) in
/-- The atlas of `X¹`: the level charts of all charts of the structure of `X`. -/
def levelAtlas : MAtlas (P.Level 1) where
  charts := {χ | ∃ (φ : MChart X) (hφ : P.IsChart φ) (x₀ : P.Level 1), χ = levelChart hφ x₀}
  compatible := by
    rintro _ ⟨φ, hφ, x₀, rfl⟩ _ ⟨ψ, hψ, y₀, rfl⟩
    exact levelChart_compatible hφ x₀ hψ y₀
  cover x := by
    obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source (P.levelVal 1 x)
    exact ⟨levelChart hφ x, ⟨φ, hφ, x, rfl⟩, hx⟩

variable (P) in
/-- **The M-polyfold `X¹`** (the paragraph after Definition 2.3.8 (preprint 2.14)): the level `X_1` with the charts
`(V₁, φ, (O₁, C₁, E¹))`.  Paracompactness of `X¹` is an instance argument, proved (Theorem 2.3.10 (preprint 2.16))
by the instance `MPolyfold.paracompactSpace_level` in `Metrizable.lean`. -/
def shift [ParacompactSpace (P.Level 1)] : MPolyfold (P.Level 1) where
  atlas := P.levelAtlas

theorem shift_isChart [ParacompactSpace (P.Level 1)] {φ : MChart X} (hφ : P.IsChart φ)
    (x₀ : P.Level 1) : P.shift.IsChart (levelChart hφ x₀) :=
  P.shift.isChart_of_mem ⟨φ, hφ, x₀, rfl⟩

end MPolyfold

end Polyfold
