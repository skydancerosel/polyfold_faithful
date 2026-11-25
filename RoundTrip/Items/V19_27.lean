import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_27

set_option maxSynthPendingDepth 3

/-! Round trip for V19_27 (2021 Proposition 19.4.5, p. 884: under properness `T` is Hausdorff and
completely regular).  Universes at `0`; the abstract lemmas `t2Space_of_orbitCharts`,
`completelyRegularSpace_of_orbitCharts` at `.{0, 0, 0, 1}` (index type `B.U.Unif : Type 1`, the level
at which `proposition_19_4_5` uses them) and `exists_invariant_urysohn` at `.{0, 0}`.  `A` =
`proposition_19_4_5` (properness = (v2), `T` = `natTop hB`) ∧ `isOrbitChart_unif` ∧
`exists_unif_π_eq` ∧ the three abstract lemmas.  `B` reads properness as (v1) for every
representative `F` and `T` as `generateFrom NatOpen`.  Glue as in V19_29.  The proof-step conjuncts
are re-proved outright (the project's proofs, copied, with the averaging lemma and
`IsOrbitChart.exists_urysohn` copied too, since the latter uses the item's
`exists_invariant_urysohn`). -/

namespace RoundTrip.V19_27
open Polyfold Polyfold.GroupoidalCategory Filter Topology

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_5.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.isOrbitChart_unif.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.exists_unif_π_eq.{0}) ∧
  (type_of% @Polyfold.Chapter19.t2Space_of_orbitCharts.{0, 0, 0, 1}) ∧
  (type_of% @Polyfold.Chapter19.completelyRegularSpace_of_orbitCharts.{0, 0, 0, 1}) ∧
  (type_of% @Polyfold.Chapter19.exists_invariant_urysohn.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_5.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.isOrbitChart_unif.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.exists_unif_π_eq.{0},
    @Polyfold.Chapter19.t2Space_of_orbitCharts.{0, 0, 0, 1},
    @Polyfold.Chapter19.completelyRegularSpace_of_orbitCharts.{0, 0, 0, 1},
    @Polyfold.Chapter19.exists_invariant_urysohn.{0, 0}⟩

theorem natT_eq {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers) : natT B.U = B.natTop hB :=
  TopologicalSpace.generateFrom_setOfPred_isOpen (B.natTop hB)

/-- `T^F_{Ψ,Ψ'}` is the topology of `B.M Ψ Ψ'` for a representative `F`. -/
theorem topology_eq {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    {F : B.U.TransitionData} (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕)
    (Ψ Ψ' : B.U.Unif) : F.topology Ψ Ψ' = B.rep.topology Ψ Ψ' :=
  TopologicalSpace.ext (funext fun _ => propext (B.isOpen_M_iff hF).symm)

theorem tendsto_iff_of_eq {X : Type} {t₁ t₂ : TopologicalSpace X} (h : t₁ = t₂) (f : ℕ → X)
    (x : X) : @Tendsto ℕ X f atTop (@nhds X t₁ x) ↔ @Tendsto ℕ X f atTop (@nhds X t₂ x) := by
  subst h; rfl

theorem V1_iff {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    {F : B.U.TransitionData} (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕) :
    V1 F ↔ B.PropernessV1 := by
  constructor
  · intro hv Ψ o
    obtain ⟨W, hWo, hoW, hW⟩ := hv Ψ o
    refine ⟨W, hWo, hoW, fun Ψ' h hs p hp => ?_⟩
    obtain ⟨φ, x, hφ, hx⟩ := hW Ψ' h hs ⟨p, hp⟩
    exact ⟨φ, hφ, x, (tendsto_iff_of_eq (topology_eq B hF Ψ Ψ') _ _).1 hx⟩
  · intro hv Ψ o
    obtain ⟨W, hWo, hoW, hW⟩ := hv Ψ o
    refine ⟨W, hWo, hoW, fun Ψ' h hs ⟨p, hp⟩ => ?_⟩
    obtain ⟨φ, hφ, x, hx⟩ := hW Ψ' h hs p hp
    exact ⟨φ, x, hφ, (tendsto_iff_of_eq (topology_eq B hF Ψ Ψ') _ _).2 hx⟩

theorem main_A_to_B
    (hA : type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_5.{0}) :
    B := by
  intro C B F hB hF hv
  rw [V1_iff B hF] at hv
  rw [natT_eq B hB]
  exact hA B hB (B.propernessV2_of_v3Lim hB (B.propernessV3Lim_of_v1 hB hv))

theorem A_to_B : A → B := fun hA => main_A_to_B hA.1

/-- `q ↦ |Ψ(q)|` is an orbit chart (re-proved outright: the item lists `isOrbitChart_unif`). -/
theorem isOrbitChart_unif' {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers) (Ψ : B.U.Unif) :
    @Chapter19.IsOrbitChart Ψ.1.G _ Ψ.1.O _ _ C.OrbitSpace (B.natTop hB)
      (fun q => C.π (Ψ.1.obj q)) :=
  B.isOrbitChart hB Ψ.2.choose_spec

/-- (v2) ⇒ (v3Lim), the project's `propernessV3Lim_of_v2` with `isOrbitChart_unif'` (the original
goes through the item's `isOrbitChart_unif`). -/
theorem v3Lim_of_v2' {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers) (hv : B.PropernessV2 hB) : B.PropernessV3Lim hB := by
  let _inst := B.natTop hB
  intro Ψ o
  have := Ψ.1.continuousConstSMul
  have := Ψ.1.P.metrizableSpace
  exact (isOrbitChart_unif' B hB Ψ).orbitChartV3Lim_of_v2 (hv Ψ o)

theorem main_B_to_A (hB' : B) :
    type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_5.{0} := by
  intro C B hB hv
  have hv' := (V1_iff B B.mk_rep).2 (B.propernessV1_of_v3Lim hB (v3Lim_of_v2' B hB hv))
  have h := hB' C B B.rep hB B.mk_rep hv'
  rwa [natT_eq B hB] at h

/-! ### The proof-step conjuncts, re-proved outright (the project's proofs, copied) -/

theorem exists_unif_π_eq' {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers) (z : C.OrbitSpace) :
    ∃ (Ψ : B.U.Unif) (o : Ψ.1.O), C.π (Ψ.1.obj o) = z := by
  obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
  obtain ⟨o, ho⟩ := B.U.isAt α Ψ hΨ
  exact ⟨⟨Ψ, α, hΨ⟩, o, by change C.π (Ψ.obj o) = z; rw [ho, hα]⟩

section Copies
open Set Function TopologicalSpace Polyfold.Chapter19
universe u v w
variable {Z : Type w} [TopologicalSpace Z]
variable {G : Type u} [Group G] {O : Type v} [TopologicalSpace O] [MulAction G O]

/-- **Serves Proposition 19.4.5** (p. 884, the averaging step, which the text leaves open): for a
finite group acting continuously on a normal `T₁` space `O` (for instance a metrizable one), a point
`ō` and a `G`-invariant open `V ∋ ō`, there is a continuous `G`-invariant `β : O → [0,1]` with
`β(ō) = 0` and `β = 1` off `V`. Averaging a `β₀` that only vanishes at `ō` gives
`β(ō) = (1/#G) ∑_g β₀(g ō)`, which need not vanish; here `β₀` vanishes on the finite closed orbit
`G·ō` (Urysohn, `exists_continuous_zero_one_of_isClosed`), and its average keeps `β(ō) = 0`. -/
theorem exists_invariant_urysohn' [Finite G] [ContinuousConstSMul G O] [NormalSpace O] [T1Space O]
    (o : O) {V : Set O} (hV : IsOpen V) (hVinv : ∀ g : G, ∀ x ∈ V, g • x ∈ V) (ho : o ∈ V) :
    ∃ β : O → ℝ, Continuous β ∧ β o = 0 ∧ (∀ x, x ∉ V → β x = 1) ∧
      (∀ x, β x ∈ Icc (0 : ℝ) 1) ∧ ∀ (g : G) (x : O), β (g • x) = β x := by
  let _ := Fintype.ofFinite G
  have hF : IsClosed (range fun g : G => g • o) := (finite_range _).isClosed
  have hd : Disjoint (range fun g : G => g • o) Vᶜ := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨g, rfl⟩ h
    exact h (hVinv g o ho)
  obtain ⟨β₀, h0, h1, h01⟩ := exists_continuous_zero_one_of_isClosed hF hV.isClosed_compl hd
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun x => (Fintype.card G : ℝ)⁻¹ * ∑ g : G, β₀ (g • x), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.mul (continuous_finsetSum _ fun g _ =>
      β₀.continuous.comp (continuous_const_smul g))
  · simp only
    rw [Finset.sum_eq_zero fun g _ => h0 ⟨g, rfl⟩, mul_zero]
  · intro x hx
    simp only
    have : ∀ g : G, β₀ (g • x) = 1 := fun g => h1 fun hgx => hx (by
      simpa using hVinv g⁻¹ _ hgx)
    rw [Finset.sum_congr rfl fun g _ => this g, Finset.sum_const, Finset.card_univ, nsmul_one,
      inv_mul_cancel₀ hcard]
  · intro x
    have hpos : (0 : ℝ) < Fintype.card G := Nat.cast_pos.2 Fintype.card_pos
    refine ⟨mul_nonneg (inv_nonneg.2 hpos.le) (Finset.sum_nonneg fun g _ => (h01 _).1), ?_⟩
    rw [inv_mul_le_iff₀ hpos, mul_one]
    calc ∑ g : G, β₀ (g • x) ≤ ∑ _g : G, (1 : ℝ) := Finset.sum_le_sum fun g _ => (h01 _).2
      _ = Fintype.card G := by simp
  · intro g x
    simp only
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun k => by simp [mul_smul]

variable {π : O → Z}


/-- **Serves Proposition 19.4.5** (p. 884, completely regular part): for an orbit chart `π : O → Z`
(`O` normal `T₁`, `G` finite) satisfying (v2) at `ō`, and a closed `A ∌ π(ō)`, there is a continuous
`f : Z → [0,1]` with `f(π ō) = 0` and `f = 1` on `A`. The text's construction: `V` the `G`-saturation
of `U(ō) \ π⁻¹(A)`, an invariant `β` from `exists_invariant_urysohn'` (the averaging), descended to
`π(O)` and extended by `1`; it is continuous on `π(O)` since `π` is open, and equal to `1` off
`cl_Z π(V) ⊆ π(O)` by (v2). -/
theorem exists_urysohn' [Finite G] [ContinuousConstSMul G O] [NormalSpace O] [T1Space O]
    (h : IsOrbitChart G π) {o : O} (hv : OrbitChartV2 π o) {A : Set Z} (hA : IsClosed A)
    (hoA : π o ∉ A) : ∃ f : Z → unitInterval, Continuous f ∧ f (π o) = 0 ∧ EqOn f 1 A := by
  obtain ⟨U, hUo, hoU, hU⟩ := hv
  set U₀ := U ∩ π ⁻¹' Aᶜ with hU₀
  have hU₀o : IsOpen U₀ := hUo.inter (hA.isOpen_compl.preimage h.continuous)
  set V := ⋃ g : G, (fun x : O => g • x) ⁻¹' U₀ with hV
  have hVo : IsOpen V := isOpen_iUnion fun g => hU₀o.preimage (continuous_const_smul g)
  have hVinv : ∀ g : G, ∀ x ∈ V, g • x ∈ V := by
    intro g x hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨k * g⁻¹, by simpa [mul_smul] using hk⟩
  have hoU₀ : o ∈ U₀ := ⟨hoU, hoA⟩
  have hoV : o ∈ V := mem_iUnion.2 ⟨1, by simpa using hoU₀⟩
  have himV : π '' V ⊆ π '' U₀ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, hg⟩ := mem_iUnion.1 hx
    exact ⟨g • x, hg, h.apply_smul g x⟩
  have hclV : closure (π '' V) ⊆ range π :=
    (closure_mono (himV.trans (image_mono inter_subset_left))).trans hU
  have hAV : ∀ x ∈ V, π x ∉ A := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := himV ⟨x, hx, rfl⟩
    rw [← hyx]
    exact hy.2
  obtain ⟨β, hβc, hβo, hβ1, hβI, hβinv⟩ := exists_invariant_urysohn' (G := G) o hVo hVinv hoV
  classical
  set ψ : Z → ℝ := fun z => if hz : z ∈ range π then β hz.choose else 1 with hψ
  have hψπ : ∀ x, ψ (π x) = β x := by
    intro x
    have hz : π x ∈ range π := mem_range_self x
    simp only [hψ, dif_pos hz]
    obtain ⟨g, hg⟩ := (h.eq_iff hz.choose x).1 hz.choose_spec
    exact (hβinv g _).symm.trans (congrArg β hg)
  have hψ1 : ∀ z, z ∉ π '' V → ψ z = 1 := by
    intro z hz
    by_cases hr : z ∈ range π
    · obtain ⟨x, rfl⟩ := hr
      rw [hψπ]
      exact hβ1 x fun hx => hz ⟨x, hx, rfl⟩
    · simp only [hψ, dif_neg hr]
  have hψc : Continuous ψ := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    by_cases hz : z ∈ closure (π '' V)
    · obtain ⟨x, rfl⟩ := hclV hz
      have : Tendsto (ψ ∘ π) (𝓝 x) (𝓝 (ψ (π x))) := by
        rw [hψπ]
        exact (hβc.tendsto x).congr fun y => (hψπ y).symm
      exact (tendsto_map'_iff.2 this).mono_left (h.isOpenMap.nhds_le x)
    · have hev : ψ =ᶠ[𝓝 z] fun _ => (1 : ℝ) :=
        mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hz) fun z' hz' =>
          hψ1 z' fun h' => hz' (subset_closure h')
      exact continuousAt_const.congr hev.symm
  refine ⟨Set.projIcc 0 1 zero_le_one ∘ ψ, continuous_projIcc.comp hψc, ?_, ?_⟩
  · simp only [Function.comp_apply, hψπ, hβo]
    exact Set.projIcc_left _
  · intro z hz
    have : ψ z = 1 := hψ1 z fun ⟨x, hx, hxz⟩ => hAV x hx (hxz ▸ hz)
    simp only [Function.comp_apply, this, Pi.one_apply]
    exact Set.projIcc_right _

/-! #### A family of orbit charts covering `Z` -/

variable {ι : Type*} {G : ι → Type u} [∀ i, Group (G i)] [∀ i, Finite (G i)] {O : ι → Type v}
  [∀ i, TopologicalSpace (O i)] [∀ i, MulAction (G i) (O i)] [∀ i, ContinuousConstSMul (G i) (O i)]
  {π : ∀ i, O i → Z}

/-- **Serves Proposition 19.4.5** (p. 884), Hausdorff: if orbit charts `π_i : O_i → Z` (with
Hausdorff `O_i`; for `|S|`, the `|Ψ|` of all uniformizers) cover `Z` and satisfy (v2) everywhere,
then `Z` is Hausdorff. -/
theorem t2Space_of_orbitCharts' [∀ i, T2Space (O i)] (hπ : ∀ i, IsOrbitChart (G i) (π i))
    (hcov : ∀ z : Z, ∃ i o, π i o = z) (hv : ∀ i o, OrbitChartV2 (π i) o) : T2Space Z := by
  refine t2Space_of_forall_closure_subset_t2 fun z => ?_
  obtain ⟨i, o, rfl⟩ := hcov z
  obtain ⟨U, hUo, hoU, hU⟩ := hv i o
  exact ⟨range (π i), (hπ i).isOpen_range, (hπ i).t2Space_range, π i '' U,
    (hπ i).isOpenMap _ hUo, mem_image_of_mem _ hoU, hU⟩

/-- **Proposition 19.4.5** (p. 884) in abstract form: if orbit charts `π_i : O_i → Z` with metrizable
`O_i` and finite groups cover `Z` and satisfy the properness condition (v2) everywhere, then `Z` is
Hausdorff and completely regular. -/
theorem completelyRegularSpace_of_orbitCharts' [∀ i, MetrizableSpace (O i)]
    (hπ : ∀ i, IsOrbitChart (G i) (π i)) (hcov : ∀ z : Z, ∃ i o, π i o = z)
    (hv : ∀ i o, OrbitChartV2 (π i) o) : T2Space Z ∧ CompletelyRegularSpace Z := by
  refine ⟨t2Space_of_orbitCharts' hπ hcov hv, ⟨fun z A hA hz => ?_⟩⟩
  obtain ⟨i, o, rfl⟩ := hcov z
  exact exists_urysohn' (hπ i) (hv i o) hA hz

end Copies

theorem B_to_A : B → A := fun hB' =>
  ⟨main_B_to_A hB', @isOrbitChart_unif', @exists_unif_π_eq', @t2Space_of_orbitCharts',
    @completelyRegularSpace_of_orbitCharts', @exists_invariant_urysohn'⟩

#rt_check RoundTrip.V19_27.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_5,
  Polyfold.GroupoidalCategory.BasicConstruction.isOrbitChart_unif,
  Polyfold.GroupoidalCategory.BasicConstruction.exists_unif_π_eq,
  Polyfold.Chapter19.t2Space_of_orbitCharts,
  Polyfold.Chapter19.completelyRegularSpace_of_orbitCharts,
  Polyfold.Chapter19.exists_invariant_urysohn]
#rt_check RoundTrip.V19_27.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_5,
  Polyfold.GroupoidalCategory.BasicConstruction.isOrbitChart_unif,
  Polyfold.GroupoidalCategory.BasicConstruction.exists_unif_π_eq,
  Polyfold.Chapter19.t2Space_of_orbitCharts,
  Polyfold.Chapter19.completelyRegularSpace_of_orbitCharts,
  Polyfold.Chapter19.exists_invariant_urysohn]
#rt_check RoundTrip.V19_27.main_A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_5,
  Polyfold.GroupoidalCategory.BasicConstruction.isOrbitChart_unif,
  Polyfold.GroupoidalCategory.BasicConstruction.exists_unif_π_eq,
  Polyfold.Chapter19.t2Space_of_orbitCharts,
  Polyfold.Chapter19.completelyRegularSpace_of_orbitCharts,
  Polyfold.Chapter19.exists_invariant_urysohn]
#rt_check RoundTrip.V19_27.main_B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_5,
  Polyfold.GroupoidalCategory.BasicConstruction.isOrbitChart_unif,
  Polyfold.GroupoidalCategory.BasicConstruction.exists_unif_π_eq,
  Polyfold.Chapter19.t2Space_of_orbitCharts,
  Polyfold.Chapter19.completelyRegularSpace_of_orbitCharts,
  Polyfold.Chapter19.exists_invariant_urysohn]
#rt_overlap RoundTrip.V19_27.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_5,
  Polyfold.GroupoidalCategory.BasicConstruction.isOrbitChart_unif,
  Polyfold.GroupoidalCategory.BasicConstruction.exists_unif_π_eq,
  Polyfold.Chapter19.t2Space_of_orbitCharts,
  Polyfold.Chapter19.completelyRegularSpace_of_orbitCharts,
  Polyfold.Chapter19.exists_invariant_urysohn]

end RoundTrip.V19_27
