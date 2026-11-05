import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_14

/-! Round trip for V2_14 (the filtration `X_m` of an M-polyfold, after Definition 2.14).

`A` is the conjunction of the types of `Polyfold.MPolyfold.mem_levelSet_iff`,
`Polyfold.MPolyfold.levelSet_zero`, `Polyfold.MPolyfold.levelSet_succ_subset`,
`Polyfold.MPolyfold.continuous_levelVal` and `Polyfold.MPolyfold.isEmbedding_levelLift`,
universe instantiated at `0` (B lives in `Type`).  `levelSet`, `smoothSet`, `levelTopology` and
`Level` are definitions (vocabulary); B characterizes them.

Glue: the project's `φ(x) ∈ range ι_m` is B's `∃ z ∈ O_m, ι_m z = φ(x)` (`φ(x) ∈ O` anyway); the
project's generators `{x ∈ V | levelLift φ m x ∈ W}` are B's traces
`{x ∈ V | ∃ z ∈ W ∩ O_m, ι_m z = φ(x)}` once `ι_m (levelLift φ m x) = φ(x)` on `X_m ∩ V`, which
needs the chart independence (A's `mem_levelSet_iff` in `A → B`, B's (1)+(2) in `B → A`; the
project's `toBase_levelLift` is built on the banned lemma and is not used).  B's extra claim that
the family is a *basis* (the project explicitly does not prove it) follows from A's
`isEmbedding_levelLift`: an open set of `X_m` meets `V_m` in `levelLift⁻¹(W)`.

`B → A`: `mem_levelSet_iff`, `levelSet_zero`, `levelSet_succ_subset` follow from B.
`continuous_levelVal` (`X_m → X` continuous) and `isEmbedding_levelLift` (`V_m ≅ O_m`) are not in
the paragraph formalized by B; they are re-proved directly with the project's arguments, taking
`ι_m (levelLift φ m x) = φ(x)` from B. -/

namespace RoundTrip.V2_14
open Polyfold Set Topology TopologicalSpace

/-- The project's statement, universe instantiated at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.mem_levelSet_iff.{0}) ∧
    (type_of% @Polyfold.MPolyfold.levelSet_zero.{0}) ∧
    (type_of% @Polyfold.MPolyfold.levelSet_succ_subset.{0}) ∧
    (type_of% @Polyfold.MPolyfold.continuous_levelVal.{0}) ∧
    (type_of% @Polyfold.MPolyfold.isEmbedding_levelLift.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.mem_levelSet_iff.{0}, @Polyfold.MPolyfold.levelSet_zero.{0},
    @Polyfold.MPolyfold.levelSet_succ_subset.{0}, @Polyfold.MPolyfold.continuous_levelVal.{0},
    @Polyfold.MPolyfold.isEmbedding_levelLift.{0}⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- The project's `X_m` is B's (definitional). -/
theorem levelSet_eq (m : ℕ) : P.levelSet m = levelSetB P m := by
  ext x
  constructor
  · rintro ⟨φ, hφ, hx, z, hz⟩
    refine ⟨φ, hφ, hx, z, ?_, hz⟩
    change φ.model.E.toBase m z ∈ φ.model.O
    rw [hz]; exact φ.mapsTo_model x hx
  · rintro ⟨φ, hφ, hx, z, -, hz⟩
    exact ⟨φ, hφ, hx, z, hz⟩

/-- Chart independence, in the form used below. -/
def Indep (P : MPolyfold X) : Prop :=
  ∀ (m : ℕ) (φ : MChart X), P.IsChart φ → ∀ x ∈ φ.source, x ∈ P.levelSet m →
    φ x ∈ range (φ.model.E.toBase m)

variable {P}

theorem toBase_levelLift' (hI : Indep P) {m : ℕ} {φ : MChart X} (hφ : P.IsChart φ) {x : X}
    (hx : x ∈ φ.source) (hxm : x ∈ P.levelSet m) :
    φ.model.E.toBase m (MPolyfold.levelLift φ m x) = φ x :=
  Function.invFun_eq (hI m φ hφ x hx hxm)

/-- The project's generators are B's traces. -/
theorem levelBasis_eq (hI : Indep P) (m : ℕ) :
    levelBasisOn P m (P.levelSet m) = P.levelBasis m := by
  have key : ∀ (φ : MChart X), P.IsChart φ → ∀ (W : Set (φ.model.E m)) (x : P.levelSet m),
      ((x : X) ∈ φ.source ∧ ∃ z ∈ W ∩ φ.model.E.lvlSet φ.model.O m,
        φ.model.E.toBase m z = φ x) ↔
      ((x : X) ∈ φ.source ∧ MPolyfold.levelLift φ m (x : X) ∈ W) := by
    intro φ hφ W x
    constructor
    · rintro ⟨hx, z, hz, hzx⟩
      refine ⟨hx, ?_⟩
      have : z = MPolyfold.levelLift φ m x :=
        φ.model.E.toBase_injective m (by rw [hzx, toBase_levelLift' hI hφ hx x.2])
      rw [← this]; exact hz.1
    · rintro ⟨hx, hW⟩
      refine ⟨hx, _, ⟨hW, ?_⟩, toBase_levelLift' hI hφ hx x.2⟩
      change φ.model.E.toBase m _ ∈ φ.model.O
      rw [toBase_levelLift' hI hφ hx x.2]; exact φ.mapsTo_model _ hx
  ext s
  constructor
  · rintro ⟨_, ⟨φ, hφ, W, hW, rfl⟩, rfl⟩
    refine ⟨φ, hφ, W, hW, ?_⟩
    ext x
    exact key φ hφ W x
  · rintro ⟨φ, hφ, W, hW, rfl⟩
    refine ⟨_, ⟨φ, hφ, W, hW, rfl⟩, ?_⟩
    ext x
    exact key φ hφ W x

/-- The generators form a basis, given that `V_m → E_m` is an embedding for every chart. -/
theorem isBasis_of_emb (m : ℕ) (hemb : ∀ {φ : MChart X}, P.IsChart φ →
      IsEmbedding fun x : (P.levelVal m ⁻¹' φ.source : Set (P.Level m)) =>
        MPolyfold.levelLift φ m (P.levelVal m x)) :
    @IsTopologicalBasis _ (P.levelTopology m) (P.levelBasis m) := by
  let _ : TopologicalSpace (P.levelSet m) := P.levelTopology m
  refine isTopologicalBasis_of_isOpen_of_nhds
    (fun u hu => TopologicalSpace.isOpen_generateFrom_of_mem hu) ?_
  intro a u hau hu
  obtain ⟨φ, hφ, ha⟩ := P.exists_isChart_mem_source (a : X)
  have he := hemb hφ
  have hu' : IsOpen (Subtype.val ⁻¹' (u : Set (P.Level m)) :
      Set (P.levelVal m ⁻¹' φ.source : Set (P.Level m))) :=
    continuous_subtype_val.isOpen_preimage _ hu
  obtain ⟨W, hW, hWeq⟩ := he.isInducing.isOpen_iff.1 hu'
  refine ⟨{y | (y : X) ∈ φ.source ∧ MPolyfold.levelLift φ m (y : X) ∈ W},
    ⟨φ, hφ, W, hW, rfl⟩, ⟨ha, ?_⟩, ?_⟩
  · have : (⟨a, ha⟩ : (P.levelVal m ⁻¹' φ.source : Set (P.Level m))) ∈
        (Subtype.val ⁻¹' (u : Set (P.Level m)) :
          Set (P.levelVal m ⁻¹' φ.source : Set (P.Level m))) := hau
    rw [← hWeq] at this; exact this
  · intro y hy
    have : (⟨y, hy.1⟩ : (P.levelVal m ⁻¹' φ.source : Set (P.Level m))) ∈
        (fun x : (P.levelVal m ⁻¹' φ.source : Set (P.Level m)) =>
          MPolyfold.levelLift φ m (P.levelVal m x)) ⁻¹' W := hy.2
    rw [hWeq] at this; exact this

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hmem, hzero, hsucc, -, hemb⟩ X _ _ _ P
  have hI : Indep P := fun m φ hφ x hx hxm => (hmem P hφ hx).1 hxm
  refine ⟨levelSet_eq P, ?_, fun m => ?_, ?_, fun m => ?_, ?_⟩
  · intro m x hx φ hφ hxφ
    rw [← levelSet_eq] at hx
    obtain ⟨z, hz⟩ := (hmem P hφ hxφ).1 hx
    refine ⟨z, ?_, hz⟩
    change φ.model.E.toBase m z ∈ φ.model.O
    rw [hz]; exact φ.mapsTo_model x hxφ
  · rw [levelBasis_eq hI m]
    exact ⟨rfl, isBasis_of_emb m fun hφ => hemb P hφ m⟩
  · rw [← levelSet_eq]; exact hzero P
  · rw [← levelSet_eq, ← levelSet_eq]; exact hsucc P m
  · change ⋂ m, P.levelSet m = _
    simp_rw [levelSet_eq]

/-! ### `B → A` -/

section Direct

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

theorem indep_of_B (hB : B) : Indep P := by
  intro m φ hφ x hx hxm
  rw [((hB X P).1 m)] at hxm
  obtain ⟨z, -, hz⟩ := (hB X P).2.1 m x hxm φ hφ hx
  exact ⟨z, hz⟩

/-- `X_m → X` is continuous (the project's argument). -/
theorem continuous_levelVal' (hI : Indep P) (m : ℕ) : Continuous (P.levelVal m) := by
  rw [continuous_def]
  intro V hV
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source (P.levelVal m x)
  obtain ⟨W, hW, hWeq⟩ := φ.exists_isOpen_image_eq (s := V ∩ φ.source) inter_subset_right
    (hV.inter φ.isOpen_source)
  refine ⟨{y : P.Level m | P.levelVal m y ∈ φ.source ∧
    MPolyfold.levelLift φ m (P.levelVal m y) ∈ φ.model.E.lvlSet W m}, ?_,
    MPolyfold.isOpen_level_basic hφ (φ.model.E.isOpen_lvlSet hW m), ?_⟩
  · rintro y ⟨hyφ, hyW⟩
    have h1 : φ (P.levelVal m y) ∈ φ.model.O ∩ W := by
      refine ⟨φ.mapsTo_model _ hyφ, ?_⟩
      have := hyW
      rwa [ScBanach.mem_lvlSet, toBase_levelLift' hI hφ hyφ (MPolyfold.levelVal_mem y)] at this
    rw [← hWeq] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    have : z = P.levelVal m y := φ.toPartialEquiv.injOn hz.2 hyφ hzeq
    rw [mem_preimage, ← this]; exact hz.1
  · refine ⟨hxφ, ?_⟩
    rw [ScBanach.mem_lvlSet, toBase_levelLift' hI hφ hxφ (MPolyfold.levelVal_mem x)]
    have : φ (P.levelVal m x) ∈ φ '' (V ∩ φ.source) := ⟨_, ⟨hx, hxφ⟩, rfl⟩
    rw [hWeq] at this
    exact this.2

/-- `V_m → E_m` is an embedding (the project's argument). -/
theorem isEmbedding_levelLift' (hI : Indep P) {φ : MChart X} (hφ : P.IsChart φ) (m : ℕ) :
    IsEmbedding fun x : (P.levelVal m ⁻¹' φ.source : Set (P.Level m)) =>
      MPolyfold.levelLift φ m (P.levelVal m x) := by
  set f := fun x : (P.levelVal m ⁻¹' φ.source : Set (P.Level m)) =>
    MPolyfold.levelLift φ m (P.levelVal m x) with hf
  have hbase : ∀ x : (P.levelVal m ⁻¹' φ.source : Set (P.Level m)),
      φ.model.E.toBase m (f x) = φ (P.levelVal m x) := fun x =>
    toBase_levelLift' hI hφ x.2 (MPolyfold.levelVal_mem x.1)
  refine ⟨⟨le_antisymm ?_ ?_⟩, ?_⟩
  · rw [← continuous_iff_le_induced]
    rw [continuous_def]
    intro W hW
    have := (MPolyfold.isOpen_level_basic hφ hW).preimage
      (continuous_subtype_val (p := fun x : P.Level m => x ∈ P.levelVal m ⁻¹' φ.source))
    convert this using 1
    ext x
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  · change TopologicalSpace.induced f _ ≤ TopologicalSpace.induced Subtype.val
      (TopologicalSpace.generateFrom (P.levelBasis m))
    rw [induced_generateFrom_eq]
    refine TopologicalSpace.le_generateFrom_iff_subset_isOpen.2 ?_
    rintro _ ⟨_, ⟨ψ, hψ, W, hW, rfl⟩, rfl⟩
    obtain ⟨W₀, hW₀, hW₀eq⟩ := φ.exists_isOpen_image_eq (s := φ.source ∩ ψ.source)
      inter_subset_left (φ.isOpen_source.inter ψ.isOpen_source)
    have hcont : ContinuousOn (levelMap (φ.transition ψ) m) (φ.model.E.lvlSet (φ.overlap ψ) m) :=
      (hφ.compatible hψ (P := P)).1.continuousOn_levelMap (φ.isScRetract_overlap ψ) m
    obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hcont) W hW
    have hov : φ.overlap ψ = φ.model.O ∩ W₀ := hW₀eq
    refine isOpen_induced_iff.2 ⟨φ.model.E.lvlSet W₀ m ∩ u,
      (φ.model.E.isOpen_lvlSet hW₀ m).inter hu, ?_⟩
    ext x
    have hxV : P.levelVal m x ∈ φ.source := x.2
    have hxO : φ (P.levelVal m x) ∈ φ.model.O := φ.mapsTo_model _ hxV
    change (f x ∈ φ.model.E.lvlSet W₀ m ∧ f x ∈ u) ↔
      (P.levelVal m x ∈ ψ.source ∧ MPolyfold.levelLift ψ m (P.levelVal m x) ∈ W)
    have hz1 : f x ∈ φ.model.E.lvlSet (φ.overlap ψ) m ↔ P.levelVal m x ∈ ψ.source := by
      rw [ScBanach.mem_lvlSet, hbase]
      constructor
      · rintro ⟨y, hy, hyeq⟩
        rw [← φ.toPartialEquiv.injOn hy.1 hxV hyeq]; exact hy.2
      · intro h; exact ⟨_, ⟨hxV, h⟩, rfl⟩
    have hz2 : MPolyfold.levelLift ψ m (P.levelVal m x) =
        levelMap (φ.transition ψ) m (f x) := by
      change Function.invFun (ψ.model.E.toBase m) (ψ (P.levelVal m x)) =
        Function.invFun (ψ.model.E.toBase m) (φ.transition ψ (φ.model.E.toBase m (f x)))
      rw [hbase, φ.transition_apply ψ hxV]
    rw [hz2]
    constructor
    · rintro ⟨h1, h2⟩
      have hzov : f x ∈ φ.model.E.lvlSet (φ.overlap ψ) m := by
        rw [ScBanach.mem_lvlSet, hov]
        exact ⟨by rw [hbase]; exact hxO, h1⟩
      have : f x ∈ u ∩ φ.model.E.lvlSet (φ.overlap ψ) m := ⟨h2, hzov⟩
      rw [← hueq] at this
      exact ⟨hz1.1 hzov, this.1⟩
    · rintro ⟨h1, h2⟩
      have hzov := hz1.2 h1
      have : f x ∈ levelMap (φ.transition ψ) m ⁻¹' W ∩ φ.model.E.lvlSet (φ.overlap ψ) m :=
        ⟨h2, hzov⟩
      rw [hueq] at this
      refine ⟨?_, this.1⟩
      have h3 : φ.model.E.toBase m (f x) ∈ φ.model.O ∩ W₀ := hov ▸ hzov
      exact h3.2
  · intro x y hxy
    have h := congrArg (φ.model.E.toBase m) hxy
    simp only [hbase] at h
    exact Subtype.ext (MPolyfold.level_ext (φ.toPartialEquiv.injOn x.2 y.2 h))

end Direct

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {X} _ _ _ P m φ hφ x hx => ?_, fun {X} _ _ _ P => ?_,
    fun {X} _ _ _ P m => ?_, fun {X} _ _ _ P m => continuous_levelVal' (indep_of_B hB) m,
    fun {X} _ _ _ P φ hφ m => isEmbedding_levelLift' (indep_of_B hB) hφ m⟩
  · constructor
    · exact indep_of_B hB m φ hφ x hx
    · intro h; exact ⟨φ, hφ, hx, h⟩
  · rw [(hB X P).1 0]; exact (hB X P).2.2.2.1
  · rw [(hB X P).1 m, (hB X P).1 (m + 1)]; exact (hB X P).2.2.2.2.1 m

#rt_check RoundTrip.V2_14.A_to_B [Polyfold.MPolyfold.mem_levelSet_iff,
  Polyfold.MPolyfold.levelSet_zero, Polyfold.MPolyfold.levelSet_succ_subset,
  Polyfold.MPolyfold.continuous_levelVal, Polyfold.MPolyfold.isEmbedding_levelLift]
#rt_check RoundTrip.V2_14.B_to_A [Polyfold.MPolyfold.mem_levelSet_iff,
  Polyfold.MPolyfold.levelSet_zero, Polyfold.MPolyfold.levelSet_succ_subset,
  Polyfold.MPolyfold.continuous_levelVal, Polyfold.MPolyfold.isEmbedding_levelLift]
#rt_overlap RoundTrip.V2_14.B_to_A [Polyfold.MPolyfold.mem_levelSet_iff,
  Polyfold.MPolyfold.levelSet_zero, Polyfold.MPolyfold.levelSet_succ_subset,
  Polyfold.MPolyfold.continuous_levelVal, Polyfold.MPolyfold.isEmbedding_levelLift]

end RoundTrip.V2_14
