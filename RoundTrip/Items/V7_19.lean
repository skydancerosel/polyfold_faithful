import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_19

/-! Round trip for V7_19 (p. 231: the splitting `𝐔(x) = ⨆_{g ∈ G_x} 𝐔(g)`).

`A` is the conjunction of the types of the listed theorems, universes at `0`: ten facts about an
arbitrary natural representation `R : X.NaturalRep x` (`isOpen_image_Γ`, `Γ_mem_image`,
`pairwise_disjoint_image_Γ`, `iUnion_image_Γ`, `isOpen_morOn`, `isConnected_image_Γ`,
`connectedComponentIn_morOn`, `isScDiffeoOn_src_image`, `isScDiffeoOn_tgt_image`, `Γ_index`), and
`EpGroupoid.lemma_7_8` (`NaturalRep.index` is a definition: vocabulary).  The project's
`𝐔(g)` is `Γ(g, U)`.

* `A → B`: `A`'s `lemma_7_8` with `N_g = W` for every `g` gives `U₁ ⊆ V` with `𝐔(U₁) ⊆ W`; a
  natural representation `R` with `R.U ⊆ U₁` is built by the project's construction of Theorem 7.5
  (sheets, Lemma 7.9, `mkRep`), re-assembled here with `A`'s `lemma_7_8` in place of the project's
  (`theorem_7_1` itself is not in `A` and its proof uses `lemma_7_8`, which may not be used).  Then
  `𝐔(g) := Γ(g, U)` and `A`'s ten facts give the splitting clauses of `B` (component, disjoint,
  covering, `s` and `t` sc-diffeomorphisms), while `B`'s `IsNatRepData` comes from the fields of
  `R`.
* `B → A`: `lemma_7_8` follows from `B` (take `V = int U₀` and `W = ⋃_g N_g`; then every `h`
  between points of `U` lies in `W`).  The other ten conjuncts are statements about every
  natural representation, which `B` (an existence statement) does not give; they are re-proved
  outright from the fields of `NaturalRep`, as in the project. -/

namespace RoundTrip.V7_19
open Polyfold Set Filter Topology

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.NaturalRep.isOpen_image_Γ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.Γ_mem_image.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.pairwise_disjoint_image_Γ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.iUnion_image_Γ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.isOpen_morOn.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.isConnected_image_Γ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.connectedComponentIn_morOn.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_src_image.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_tgt_image.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.Γ_index.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_7_8.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.NaturalRep.isOpen_image_Γ.{0},
    @Polyfold.EpGroupoid.NaturalRep.Γ_mem_image.{0},
    @Polyfold.EpGroupoid.NaturalRep.pairwise_disjoint_image_Γ.{0},
    @Polyfold.EpGroupoid.NaturalRep.iUnion_image_Γ.{0},
    @Polyfold.EpGroupoid.NaturalRep.isOpen_morOn.{0},
    @Polyfold.EpGroupoid.NaturalRep.isConnected_image_Γ.{0},
    @Polyfold.EpGroupoid.NaturalRep.connectedComponentIn_morOn.{0},
    @Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_src_image.{0},
    @Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_tgt_image.{0},
    @Polyfold.EpGroupoid.NaturalRep.Γ_index.{0},
    @Polyfold.EpGroupoid.lemma_7_8.{0}⟩

section Dictionary
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}

/-- The project's `G_x` element as `B`'s. -/
def toG (g : X.Isotropy x) : Gx X x := ⟨g.val, g.src_val, g.tgt_val⟩

/-- `B`'s `G_x` element as the project's. -/
def ofG (g : Gx X x) : X.Isotropy x := ⟨g.1, g.2.1, g.2.2⟩

theorem ofG_surjective : Function.Surjective (ofG : Gx X x → X.Isotropy x) :=
  fun g => ⟨toG g, rfl⟩

theorem ofG_injective : Function.Injective (ofG : Gx X x → X.Isotropy x) :=
  fun _ _ he => congrArg toG he

/-- The fields of a natural representation give `B`'s `IsNatRepData`. -/
theorem natRepData (R : X.NaturalRep x) :
    IsNatRepData X x R.U (fun g => R.Φ (ofG g)) (fun g => R.Γ (ofG g)) := by
  have hmem : ∀ g, ∀ y ∈ R.U, R.Γ g y ∈ X.morOn R.U := fun g y hy =>
    ⟨by rw [R.src_Γ g y hy]; exact hy,
      by rw [R.tgt_Γ g y hy]; exact (R.isScDiffeoOn_Φ g).mapsTo hy⟩
  refine ⟨fun g => ⟨_, R.isScDiffeoOn_Φ (ofG g)⟩, fun g h k hk y hy => ?_,
    fun g => R.isScSmoothOn_Γ (ofG g), fun g => R.Γ_self (ofG g),
    fun g y hy => ⟨R.src_Γ (ofG g) y hy, R.tgt_Γ (ofG g) y hy⟩, fun h hs ht => ?_,
    fun p hp => hmem _ p.2 hp.2, fun p hp q hq he => ?_, fun φ hφ => ?_⟩
  · have : ofG k = ofG g * ofG h := GroupoidStr.Isotropy.ext hk
    simp only [this]
    exact R.Φ_mul _ _ y hy
  · obtain ⟨g, hg, hu⟩ := R.existsUnique_Γ h hs ht
    exact ⟨toG g, hg, fun g' hg' => by
      have := hu (ofG g') hg'
      rw [← this]
      rfl⟩
  · have he0 : R.Γ (ofG p.1) p.2 = R.Γ (ofG q.1) q.2 := he
    have h2 : p.2 = q.2 := by
      have := congrArg X.src he0
      rwa [R.src_Γ _ _ hp.2, R.src_Γ _ _ hq.2] at this
    rw [h2] at he0
    have hm := hmem (ofG q.1) q.2 hq.2
    obtain ⟨k, -, hk⟩ := R.existsUnique_Γ _ hm.1 hm.2
    rw [R.src_Γ _ _ hq.2] at hk
    exact Prod.ext (ofG_injective ((hk _ he0).trans (hk _ rfl).symm)) h2
  · obtain ⟨g, hg, -⟩ := R.existsUnique_Γ φ hφ.1 hφ.2
    exact ⟨(toG g, X.src φ), ⟨mem_univ _, hφ.1⟩, hg⟩

/-- **Theorem 7.1 from a Lemma 7.8**: the project's construction (sheets, Lemma 7.9, `mkRep`),
with the given form of Lemma 7.8. -/
theorem exists_rep (h78 : type_of% @Polyfold.EpGroupoid.lemma_7_8.{0}) (X : EpGroupoid Obj Mor)
    (x : Obj) {V : Set Obj} (hV : IsOpen V) (hx : x ∈ V) : ∃ R : X.NaturalRep x, R.U ⊆ V := by
  have := EpGroupoid.NatRepConstruction.finite_isotropy X x
  obtain ⟨D⟩ := EpGroupoid.NatRepConstruction.exists_sheets X x
  have hU₀ : V ∩ ⋂ g, D.S g ∈ 𝓝 x :=
    inter_mem (hV.mem_nhds hx) (iInter_mem.2 fun g => (D.isOpen_S g).mem_nhds (D.mem_S g))
  obtain ⟨U₁, hU₁o, hxU₁, hU₁U₀, h78'⟩ := h78 X D.isOpen_N D.mem_N hU₀
  have hU₁S : ∀ g, U₁ ⊆ D.S g := fun g y hy => mem_iInter.1 (hU₁U₀ hy).2 g
  obtain ⟨U₂, hU₂o, hU₂c, hxU₂, hU₂U₁, hUU₁, hinv⟩ := X.lemma_7_9 D hU₁o hxU₁ hU₁S h78'
  have hU₂S : ∀ g, U₂ ⊆ D.S g := fun g => hU₂U₁.trans (hU₁S g)
  have hUS : ∀ g, D.unionHat U₂ ⊆ D.S g := fun g => hUU₁.trans (hU₁S g)
  exact ⟨D.mkRep _ (D.isOpen_unionHat hU₂o hU₂S) (D.isConnected_unionHat hU₂c hxU₂ hU₂S)
    (D.mem_unionHat hxU₂) hUS hinv fun h hs ht => h78' h (hUU₁ hs) (hUU₁ ht),
    fun y hy => (hU₁U₀ (hUU₁ hy)).1⟩

end Dictionary

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X x V W hV hxV hW hGW
  obtain ⟨-, hmem, hdisj, hUnion, -, -, hcc, hsrc, htgt, -, h78⟩ := hA
  -- `U₁ ⊆ V` with every morphism between points of `U₁` in `W` (Lemma 7.8 with `N_g = W`)
  obtain ⟨U₁, hU₁o, hxU₁, hU₁V, hU₁W⟩ := h78 X (N := fun _ => W) (fun _ => hW)
    (fun g => hGW ⟨g.src_val, g.tgt_val⟩) (hV.mem_nhds hxV)
  obtain ⟨R, hRU⟩ := exists_rep h78 X x hU₁o hxU₁
  have hΓx : ∀ g : Gx X x, g.1 ∈ R.Γ (ofG g) '' R.U := fun g => by
    have := hmem R (ofG g) R.mem_U
    rwa [R.Γ_self] at this
  refine ⟨R.U, fun g => R.Φ (ofG g), fun g => R.Γ (ofG g), R.isOpen_U, R.isConnected_U, R.mem_U,
    hRU.trans hU₁V, natRepData R, fun φ hφ => (hU₁W φ (hRU hφ.1) (hRU hφ.2)).elim fun _ h => h,
    fun g => R.Γ (ofG g) '' R.U, fun g => (hcc R (hΓx g)).symm,
    fun g h hgh => hdisj R fun he => hgh (ofG_injective he), ?_,
    fun g => ⟨⟨_, hsrc R (ofG g)⟩, ⟨_, htgt R (ofG g)⟩⟩⟩
  exact (ofG_surjective.iUnion_comp fun g' => R.Γ g' '' R.U).trans (hUnion R)

/-! ### `B → A`: `lemma_7_8` from `B`, the rest outright -/

/-- A continuous section of a continuous locally injective map over an open set has open image
(as in the project, where it is private). -/
theorem isOpen_image_of_section' {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
    {p : M → Y} (hp : IsLocallyInjective p) (hpc : Continuous p) {U : Set Y} (hU : IsOpen U)
    {σ : Y → M} (hσ : ContinuousOn σ U) (hsec : ∀ y ∈ U, p (σ y) = y) : IsOpen (σ '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨W, hWo, hyW, hinj⟩ := hp (σ y)
  have hN : IsOpen (U ∩ σ ⁻¹' W) := hσ.isOpen_inter_preimage hU hWo
  refine ⟨W ∩ p ⁻¹' (U ∩ σ ⁻¹' W), fun ψ hψ => ?_, hWo.inter (hN.preimage hpc), hyW, ?_⟩
  · exact ⟨p ψ, hψ.2.1, hinj hψ.2.2 hψ.1 (hsec _ hψ.2.1)⟩
  · change p (σ y) ∈ U ∩ σ ⁻¹' W
    rw [hsec y hy]
    exact ⟨hy, hyW⟩

section Outright
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}
  (R : X.NaturalRep x)

theorem isOpen_image_Γ' (g : X.Isotropy x) : IsOpen (R.Γ g '' R.U) :=
  isOpen_image_of_section' X.isLocalScDiffeo_src.isLocallyInjective X.continuous_src R.isOpen_U
    (R.isScSmoothOn_Γ g).continuousOn (R.src_Γ g)

theorem Γ_mem_image' (g : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) : R.Γ g y ∈ R.Γ g '' R.U :=
  mem_image_of_mem _ hy

theorem pairwise_disjoint_image_Γ' :
    Pairwise (Function.onFun Disjoint fun g : X.Isotropy x => R.Γ g '' R.U) := by
  intro g h hgh
  refine disjoint_left.2 ?_
  rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', he⟩
  have hyy' : y' = y := by rw [← R.src_Γ h y' hy', he, R.src_Γ g y hy]
  subst hyy'
  exact hgh ((R.Γ_inj hy).1 he.symm)

theorem iUnion_image_Γ' : ⋃ g : X.Isotropy x, R.Γ g '' R.U = X.morOn R.U := by
  refine Subset.antisymm (iUnion_subset fun g => ?_) fun φ hφ => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact R.Γ_mem_morOn g hy
  · obtain ⟨g, hg, -⟩ := R.existsUnique_Γ φ hφ.1 hφ.2
    exact mem_iUnion.2 ⟨g, X.src φ, hφ.1, hg⟩

theorem isOpen_morOn' : IsOpen (X.morOn R.U) := by
  rw [← iUnion_image_Γ' R]
  exact isOpen_iUnion (isOpen_image_Γ' R)

theorem isConnected_image_Γ' (g : X.Isotropy x) : IsConnected (R.Γ g '' R.U) :=
  R.isConnected_U.image _ (R.isScSmoothOn_Γ g).continuousOn

theorem connectedComponentIn_morOn' {g : X.Isotropy x} {φ : Mor} (hφ : φ ∈ R.Γ g '' R.U) :
    connectedComponentIn (X.morOn R.U) φ = R.Γ g '' R.U := by
  have hsub : R.Γ g '' R.U ⊆ X.morOn R.U := by
    rw [← iUnion_image_Γ' R]
    exact subset_iUnion (fun h => R.Γ h '' R.U) g
  refine Subset.antisymm ?_
    ((isConnected_image_Γ' R g).isPreconnected.subset_connectedComponentIn hφ hsub)
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union (isOpen_image_Γ' R g)
    (v := ⋃ h ∈ {h | h ≠ g}, R.Γ h '' R.U) (isOpen_biUnion fun h _ => isOpen_image_Γ' R h)
    (disjoint_iUnion₂_right.2 fun h hh => pairwise_disjoint_image_Γ' R (Ne.symm hh))
    (fun ψ hψ => ?_) ⟨φ, mem_connectedComponentIn (hsub hφ), hφ⟩
  have hψ' := connectedComponentIn_subset _ _ hψ
  rw [← iUnion_image_Γ' R] at hψ'
  obtain ⟨k, hk⟩ := mem_iUnion.1 hψ'
  by_cases hkg : k = g
  · exact Or.inl (hkg ▸ hk)
  · exact Or.inr (mem_iUnion₂.2 ⟨k, hkg, hk⟩)

theorem isScDiffeoOn_src_image' (g : X.Isotropy x) :
    X.PMor.IsScDiffeoOn X.PObj X.src (R.Γ g) (R.Γ g '' R.U) R.U where
  isScSmoothOn := X.isScSmoothMap_src.mono (isOpen_image_Γ' R g) (subset_univ _)
  isScSmoothOn_inv := R.isScSmoothOn_Γ g
  mapsTo _ hφ := R.src_mem_of_mem_image hφ
  mapsTo_inv _ hy := Γ_mem_image' R g hy
  left_inv _ hφ := R.Γ_src_of_mem_image hφ
  right_inv y hy := R.src_Γ g y hy

theorem isScDiffeoOn_tgt_image' (g : X.Isotropy x) :
    X.PMor.IsScDiffeoOn X.PObj X.tgt (fun z => R.Γ g (R.Φ g⁻¹ z)) (R.Γ g '' R.U) R.U where
  isScSmoothOn := X.isScSmoothMap_tgt.mono (isOpen_image_Γ' R g) (subset_univ _)
  isScSmoothOn_inv := MPolyfold.IsScSmoothOn.comp (R.isScSmoothOn_Γ g)
    (R.isScDiffeoOn_Φ g).isScSmoothOn_inv (R.isScDiffeoOn_Φ g).mapsTo_inv
  mapsTo := by
    rintro _ ⟨y, hy, rfl⟩
    rw [R.tgt_Γ g y hy]
    exact R.mapsTo_Φ g hy
  mapsTo_inv _ hz := Γ_mem_image' R g ((R.isScDiffeoOn_Φ g).mapsTo_inv hz)
  left_inv := by
    rintro _ ⟨y, hy, rfl⟩
    rw [R.tgt_Γ g y hy, R.Φ_inv_Φ g hy]
  right_inv z hz := by
    rw [R.tgt_Γ g _ ((R.isScDiffeoOn_Φ g).mapsTo_inv hz), R.Φ_Φ_inv g hz]

theorem Γ_index' {φ : Mor} (hφ : φ ∈ X.morOn R.U) : R.Γ (R.index φ) (X.src φ) = φ := by
  rw [EpGroupoid.NaturalRep.index, dif_pos hφ]
  exact (R.exists_Γ_eq hφ).choose_spec

end Outright

theorem B_to_A : B → A := by
  intro hB
  refine ⟨@isOpen_image_Γ', @Γ_mem_image', @pairwise_disjoint_image_Γ', @iUnion_image_Γ',
    @isOpen_morOn', @isConnected_image_Γ', @connectedComponentIn_morOn', @isScDiffeoOn_src_image',
    @isScDiffeoOn_tgt_image', @Γ_index', ?_⟩
  -- Lemma 7.8 from `B`, with `V = int U₀` and `W = ⋃_g N_g`
  intro Obj Mor _ _ _ _ _ _ X x N hN hgN U₀ hU₀
  obtain ⟨U, -, -, hUo, -, hxU, hUV, -, hUW, -⟩ := hB Obj Mor X x (interior U₀) (⋃ g, N g)
    isOpen_interior (mem_interior_iff_mem_nhds.2 hU₀) (isOpen_iUnion hN)
    fun g hg => mem_iUnion.2 ⟨⟨g, hg.1, hg.2⟩, hgN _⟩
  exact ⟨U, hUo, hxU, hUV.trans interior_subset, fun h hs ht => mem_iUnion.1 (hUW ⟨hs, ht⟩)⟩

#rt_check RoundTrip.V7_19.A_to_B [Polyfold.EpGroupoid.NaturalRep.isOpen_image_Γ,
  Polyfold.EpGroupoid.NaturalRep.Γ_mem_image, Polyfold.EpGroupoid.NaturalRep.pairwise_disjoint_image_Γ,
  Polyfold.EpGroupoid.NaturalRep.iUnion_image_Γ, Polyfold.EpGroupoid.NaturalRep.isOpen_morOn,
  Polyfold.EpGroupoid.NaturalRep.isConnected_image_Γ,
  Polyfold.EpGroupoid.NaturalRep.connectedComponentIn_morOn,
  Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_src_image,
  Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_tgt_image, Polyfold.EpGroupoid.NaturalRep.Γ_index,
  Polyfold.EpGroupoid.lemma_7_8]
#rt_check RoundTrip.V7_19.B_to_A [Polyfold.EpGroupoid.NaturalRep.isOpen_image_Γ,
  Polyfold.EpGroupoid.NaturalRep.Γ_mem_image, Polyfold.EpGroupoid.NaturalRep.pairwise_disjoint_image_Γ,
  Polyfold.EpGroupoid.NaturalRep.iUnion_image_Γ, Polyfold.EpGroupoid.NaturalRep.isOpen_morOn,
  Polyfold.EpGroupoid.NaturalRep.isConnected_image_Γ,
  Polyfold.EpGroupoid.NaturalRep.connectedComponentIn_morOn,
  Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_src_image,
  Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_tgt_image, Polyfold.EpGroupoid.NaturalRep.Γ_index,
  Polyfold.EpGroupoid.lemma_7_8]
#rt_overlap RoundTrip.V7_19.B_to_A [Polyfold.EpGroupoid.NaturalRep.isOpen_image_Γ,
  Polyfold.EpGroupoid.NaturalRep.Γ_mem_image, Polyfold.EpGroupoid.NaturalRep.pairwise_disjoint_image_Γ,
  Polyfold.EpGroupoid.NaturalRep.iUnion_image_Γ, Polyfold.EpGroupoid.NaturalRep.isOpen_morOn,
  Polyfold.EpGroupoid.NaturalRep.isConnected_image_Γ,
  Polyfold.EpGroupoid.NaturalRep.connectedComponentIn_morOn,
  Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_src_image,
  Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_tgt_image, Polyfold.EpGroupoid.NaturalRep.Γ_index,
  Polyfold.EpGroupoid.lemma_7_8]

end RoundTrip.V7_19
