import Polyfold.Chapter14.ZDataLocalExtension
import Polyfold.Chapter14.FiniteRepresentation
import Polyfold.Chapter14.BoundaryCover
import Polyfold.Chapter7.ProperSubsets
import Polyfold.Chapter7.Basic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
§14.4, pp. 661–662: **Proposition 14.4.6 (2)** in general (2017 text: Proposition 14.5 (2)).

# Limits of z-loops

## The text, paraphrased

(Proposition 14.4.6 (2)) If `z_k ∈ V_a`, `i ∼_{z_k} i'` and `z_k → z₀ ∈ cl_X(V_a)`, then
`s^{0a}_i = s^{0a}_{i'}` on an open neighbourhood `Q(z₀) ⊆ U(a)` of `z₀`.  (Proof) Only finitely
many `|V̂_b|` meet a neighbourhood of `|z₀|`, and only finitely many objects of the closures
`cl_X(Ũ(b))` are isomorphic to `z₀` (properness); Lemma 14.4.7 around them gives sheets; for `k`
large every morphism of a `z_k`-loop lies in one of the sheets, and the loop is carried to a loop
through the sheet centres with the same index steps, along which the boundary sections are
transported.

## What is formalized

* `ZLimitSetting S`: the facts of §14.3 that the proof uses, beyond `ZData`:
  open sets `M b c` of morphisms (Proposition 14.3.4's `Ô_{b,c}`) on which `τ̂_{b,c}` is locally
  constant, containing every morphism of `∂X` from `Ũ(b)` to `cl_X(Ũ(c))`
  (Proposition 14.3.4 (1) with `cl_X(Ũ(c)) ⊆ Ũ'(c)`); `cl_X(Ũ(b))` proper ((P6)); and
  `(|V̂_b|)_{b ∈ A}` locally finite (Proposition 14.3.8 (3)).
* `ZSections.CompatNbhd D`: Definition 14.1.7 (4) for `τ̂ = τ⁰` along the morphisms of `∂X` from
  `Ũ(b)` to `Ũ(c)` (the boundary data are defined on `U⁰(b, c) ⊇` these morphisms).
* `ZLimitRep L z₀`: the finite natural representation of the text's proof (the finite set `o` of
  indices, the objects `Y` of `⋃_{b ∈ o} cl_X(V̂_b)` isomorphic to `z₀`, Lemma 14.4.7's sheets,
  and a neighbourhood `W` of `z₀` from which every morphism into a `V̂_c` lands in the sheets);
  `ZLimitSetting.exists_limitRep` builds it at every `z₀ ∈ cl_X(V̂_a) ∩ ∂X`.
* `ZLimitRep.arc_transport`: a chain with an arc starting in `W` lies in the sheet of a morphism
  `ψ` from `z₀`, and the boundary sections are transported along the deformed chains
  `(s|𝐎(ψ))⁻¹(y)`, `y ∈ O(z₀) ∩ ∂X`.
* **Proposition 14.4.6 (2)**: `hasThetaLocalEq_of_limit` (the form `HasThetaLocalEq` with
  `z_k ∈ V̂_a`, which Lemma 14.4.9 (3) uses), `proposition_14_4_6_2_of_limit` (the printed form),
  and `sections_eq_of_theta_closure` (the same for every `z₀ ∈ cl_X(V̂_a) ∩ ∂X`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- A map locally constant at every point of a set `M` is constant on every preconnected
subset of `M`. -/
theorem eq_of_isPreconnected_z5 {α β : Type*} [TopologicalSpace α] {f : α → β} {M C : Set α}
    (hC : IsPreconnected C) (hCM : C ⊆ M) (hf : ∀ φ ∈ M, ∀ᶠ ψ in 𝓝 φ, f ψ = f φ) {x y : α}
    (hx : x ∈ C) (hy : y ∈ C) : f x = f y := by
  let _ : TopologicalSpace β := ⊥
  have _ : DiscreteTopology β := ⟨rfl⟩
  have hc : ContinuousOn f C := fun φ hφ => by
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, nhds_discrete β, tendsto_pure]
    exact hf φ (hCM hφ)
  exact hC.constant hc hx hy

namespace NaturalRepFinite

variable {Y : Finset Obj} {V : Set Obj} (N : X.NaturalRepFinite Y V)

theorem unit_mem_morOn_z5 {y : Obj} (hy : y ∈ Y) : X.unit y ∈ X.morOn (Y : Set Obj) :=
  ⟨by rw [X.src_unit]; exact hy, by rw [X.tgt_unit]; exact hy⟩

/-- The units over `O(y₀)` lie in the sheet of `1_{y₀}`. -/
theorem unit_mem_sheet_z5 {y₀ : Obj} (hy₀ : y₀ ∈ Y) {y : Obj} (hy : y ∈ N.U y₀) :
    X.unit y ∈ N.sheet (X.unit y₀) := by
  have hu := unit_mem_morOn_z5 (X := X) hy₀
  have hconn : IsConnected (X.unit '' N.U y₀) :=
    (N.isConnected_U y₀ hy₀).image X.unit X.continuous_unit.continuousOn
  have hsub : X.unit '' N.U y₀ ⊆ X.morOn (⋃ y ∈ Y, N.U y) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨by rw [X.src_unit]; exact mem_biUnion hy₀ hw,
      by rw [X.tgt_unit]; exact mem_biUnion hy₀ hw⟩
  have := hconn.isPreconnected.subset_connectedComponentIn ⟨y₀, N.mem_U y₀ hy₀, rfl⟩ hsub
  rw [NatRepFinite.connectedComponentIn_morOn N hu (N.mem_sheet _ hu)] at this
  exact this ⟨y, hy, rfl⟩

theorem srcInv_unit_z5 {y₀ : Obj} (hy₀ : y₀ ∈ Y) {y : Obj} (hy : y ∈ N.U y₀) :
    N.srcInv (X.unit y₀) y = X.unit y := by
  have := N.srcInv_src (unit_mem_morOn_z5 (X := X) hy₀) (N.unit_mem_sheet_z5 hy₀ hy)
  rwa [X.src_unit] at this

theorem eq_of_mem_U_z5 {y y' : Obj} (hy : y ∈ Y) (hy' : y' ∈ Y) {x : Obj} (hx : x ∈ N.U y)
    (hx' : x ∈ N.U y') : y = y' := by
  by_contra h
  exact Set.disjoint_left.1 (N.pairwiseDisjoint_U (Finset.mem_coe.2 hy) (Finset.mem_coe.2 hy') h)
    hx hx'

theorem eq_of_mem_sheet_z5 {ψ ψ' : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj))
    (hψ' : ψ' ∈ X.morOn (Y : Set Obj)) {φ : Mor} (h : φ ∈ N.sheet ψ) (h' : φ ∈ N.sheet ψ') :
    ψ = ψ' := by
  by_contra hne
  exact Set.disjoint_left.1 (N.pairwiseDisjoint_sheet hψ hψ' hne) h h'

theorem exists_sheet_z5 {φ : Mor} (h : φ ∈ X.morOn (⋃ y ∈ Y, N.U y)) :
    ∃ ψ ∈ X.morOn (Y : Set Obj), φ ∈ N.sheet ψ := by
  rw [N.morOn_eq] at h
  obtain ⟨ψ, hψ, hφ⟩ := mem_iUnion₂.1 h
  exact ⟨ψ, hψ, hφ⟩

end NaturalRepFinite

end EpGroupoid

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### The setting -/

/-- **The facts of §14.3 used by the proof of Proposition 14.4.6 (2)** (pp. 652–657), beyond
`ZData`: open sets `M b c` of morphisms (the `Ô_{b,c}` of Proposition 14.3.4) on which `τ̂_{b,c}`
is locally constant and which contain every morphism of `∂X` from `Ũ(b)` to `cl_X(Ũ(c))`
(Proposition 14.3.4 (1), `U'(b, c) ⊆ Ô_{b,c}`, with `cl_X(Ũ(c)) ⊆ Ũ'(c)`); the properness of
`cl_X(Ũ(b))` ((P6)); and the local finiteness of `(|V̂_b|)_{b ∈ A}` (Proposition 14.3.8 (3)). -/
structure ZLimitSetting (S : A.X.ZData) where
  /-- The open sets `Ô_{b,c}`. -/
  M : A.Obj → A.Obj → Set A.Mor
  isOpen_M : ∀ b ∈ S.A, ∀ c ∈ S.A, IsOpen (M b c)
  locallyConstant_M : ∀ b ∈ S.A, ∀ c ∈ S.A, ∀ φ ∈ M b c, ∀ᶠ ψ in 𝓝 φ, S.τ b c ψ = S.τ b c φ
  boundary_mem_M : ∀ b ∈ S.A, ∀ c ∈ S.A, ∀ φ,
    A.X.src φ ∈ (S.nbhd b).U ∩ A.X.PObj.boundary →
    A.X.tgt φ ∈ closure (S.nbhd c).U ∩ A.X.PObj.boundary → φ ∈ M b c
  isProper : ∀ b ∈ S.A, A.X.IsProperSubset (closure (S.nbhd b).U)
  locallyFinite : LocallyFinite fun b : S.A => A.X.π '' S.V b

/-- **Definition 14.1.7 (4) for `τ̂` on the morphisms of `∂X` from `Ũ(b)` to `Ũ(c)`** (there
`τ̂_{b,c} = τ⁰_{b,c}`, Proposition 14.3.4): `s^c_j(t(φ)) = μ(φ, s^b_i(s(φ)))` for every pair
`(i, j)` of `τ̂_{b,c}(φ)`. -/
def ZSections.CompatNbhd {S : A.X.ZData} (D : ZSections A S) : Prop :=
  ∀ b ∈ S.A, ∀ c ∈ S.A, ∀ φ, A.X.src φ ∈ (S.nbhd b).U ∩ A.X.PObj.boundary →
    A.X.tgt φ ∈ (S.nbhd c).U → ∀ i j, (S.τ b c φ).Pairs i j →
      D.s c j (A.X.tgt φ) = fibAct φ (D.s b i (A.X.src φ))

/-- **The finite natural representation of the proof of Proposition 14.4.6 (2)** at `z₀`: a
finite set `o ⊆ A` of indices, the finite set `Y ∋ z₀` of boundary objects (the objects of
`⋃_{b ∈ o} cl_X(V̂_b)` isomorphic to `z₀`), a natural representation `N` of `Y`
(Lemma 14.4.7), and a neighbourhood `W ⊆ O(z₀)` of `z₀` such that every morphism from `W` into
some `V̂_c` has `c ∈ o` and ends in `⋃ O(y)`; each `O(y)` misses `cl_X(V̂_b)` for `b ∈ o` with
`y ∉ cl_X(V̂_b)`, and for `y ∈ cl_X(V̂_b)` lies in `Ũ(b)` and sends its morphisms into
`cl_X(Ũ(c))` into `Ô_{b,c}`. -/
structure ZLimitRep {S : A.X.ZData} (L : ZLimitSetting S) (z₀ : A.Obj) where
  o : Set A.Obj
  o_subset : o ⊆ S.A
  Y : Finset A.Obj
  mem_Y : z₀ ∈ Y
  Y_boundary : ∀ y ∈ Y, y ∈ A.X.PObj.boundary
  V : Set A.Obj
  N : A.X.NaturalRepFinite Y V
  W : Set A.Obj
  W_mem : W ∈ 𝓝 z₀
  W_subset : W ⊆ N.U z₀
  W_tgt : ∀ φ, A.X.src φ ∈ W → ∀ c ∈ S.A, A.X.tgt φ ∈ S.V c →
    c ∈ o ∧ A.X.tgt φ ∈ ⋃ y ∈ Y, N.U y
  U_far : ∀ y ∈ Y, ∀ b ∈ o, y ∉ closure (S.V b) → Disjoint (N.U y) (closure (S.V b))
  U_near : ∀ y ∈ Y, ∀ b ∈ o, y ∈ closure (S.V b) → N.U y ⊆ (S.nbhd b).U ∧
    ∀ c ∈ o, ∀ φ, A.X.src φ ∈ N.U y → A.X.tgt φ ∈ closure (S.nbhd c).U → φ ∈ L.M b c

namespace ZLimitRep

variable {S : A.X.ZData} {L : ZLimitSetting S} {z₀ : A.Obj} (R : ZLimitRep L z₀)

theorem mem_o_of_mem_W {x : A.Obj} (hx : x ∈ R.W) {c : A.Obj} (hc : c ∈ S.A)
    (hxc : x ∈ S.V c) : c ∈ R.o :=
  (R.W_tgt (A.X.unit x) (by rw [A.X.src_unit]; exact hx) c hc (by rw [A.X.tgt_unit]; exact hxc)).1

/-- The sheet of a morphism `ω : y → y'` of `Y` with `y ∈ cl_X(V̂_b)`, `y' ∈ cl_X(V̂_c)` lies in
`Ô_{b,c}`. -/
theorem sheet_subset_M {ω : A.Mor} (hω : ω ∈ A.X.morOn (R.Y : Set A.Obj)) {b c : A.Obj}
    (hb : b ∈ R.o) (hc : c ∈ R.o) (hωb : A.X.src ω ∈ closure (S.V b))
    (hωc : A.X.tgt ω ∈ closure (S.V c)) : R.N.sheet ω ⊆ L.M b c := fun θ hθ =>
  (R.U_near _ hω.1 b hb hωb).2 c hc θ (R.N.src_mem hω hθ)
    (subset_closure ((R.U_near _ hω.2 c hc hωc).1 (R.N.tgt_mem hω hθ)))

/-- `τ̂_{b,c}` is constant on such a sheet (it is connected and lies in `Ô_{b,c}`). -/
theorem tau_eq {ω : A.Mor} (hω : ω ∈ A.X.morOn (R.Y : Set A.Obj)) {b c : A.Obj}
    (hb : b ∈ R.o) (hc : c ∈ R.o) (hωb : A.X.src ω ∈ closure (S.V b))
    (hωc : A.X.tgt ω ∈ closure (S.V c)) {θ θ' : A.Mor} (hθ : θ ∈ R.N.sheet ω)
    (hθ' : θ' ∈ R.N.sheet ω) : S.τ b c θ = S.τ b c θ' :=
  eq_of_isPreconnected_z5 (R.N.isConnected_sheet ω hω).isPreconnected
    (R.sheet_subset_M hω hb hc hωb hωc) (L.locallyConstant_M b (R.o_subset hb) c (R.o_subset hc))
    hθ hθ'

variable (D : ZSections A S)

/-- **The limit loop** (the core of the proof of Proposition 14.4.6 (2)): a chain with an arc
from `i ∈ I_a` to `j ∈ I_b` starting in `W` (with `z₀ ∈ cl_X(V̂_a)`) has its composite in the
sheet of a morphism `ψ : z₀ → y` of `Y` with `y ∈ cl_X(V̂_b)`, and along the deformed chains
`(s|𝐎(ψ))⁻¹(y')`, `y' ∈ O(z₀) ∩ ∂X`, the boundary sections are transported:
`s^b_j(t((s|𝐎(ψ))⁻¹(y'))) = μ((s|𝐎(ψ))⁻¹(y'), s^a_i(y'))`. -/
theorem arc_transport (hD : D.CompatNbhd) {a b : A.Obj} {i : S.I a} {j : S.I b} {φ : A.Mor}
    (h : S.Arc a b i j φ) : A.X.src φ ∈ R.W → z₀ ∈ closure (S.V a) →
    ∃ ψ ∈ A.X.morOn (R.Y : Set A.Obj), A.X.src ψ = z₀ ∧ A.X.tgt ψ ∈ closure (S.V b) ∧
      φ ∈ R.N.sheet ψ ∧ ∀ y ∈ R.N.U z₀ ∩ A.X.PObj.boundary,
        D.s b j (A.X.tgt (R.N.srcInv ψ y)) = fibAct (R.N.srcInv ψ y) (D.s a i y) := by
  induction h with
  | @nil ha z hz i =>
    intro hzW hz₀
    rw [A.X.src_unit] at hzW
    have hao : a ∈ R.o := R.mem_o_of_mem_W hzW ha hz
    have hu := NaturalRepFinite.unit_mem_morOn_z5 (X := A.X) R.mem_Y
    refine ⟨A.X.unit z₀, hu, A.X.src_unit z₀, by rw [A.X.tgt_unit]; exact hz₀,
      R.N.unit_mem_sheet_z5 R.mem_Y (R.W_subset hzW), fun y hy => ?_⟩
    have hyU : y ∈ (S.nbhd a).U := (R.U_near z₀ R.mem_Y a hao hz₀).1 hy.1
    rw [R.N.srcInv_unit_z5 R.mem_Y hy.1, A.X.tgt_unit,
      fibAct_unit_p3w3 (D.P_s a ha i y ⟨hyU, hy.2⟩)]
  | @snoc b c i j k φ ψ' h hc hs ht hp ih =>
    intro hW hz₀
    rw [A.X.src_comp _ _ hs] at hW
    obtain ⟨ψ, hψ, hψs, hψt, hφψ, htr⟩ := ih hW hz₀
    have hpr := h.props
    have hb : b ∈ R.o := (R.W_tgt φ hW b hpr.2.1 hpr.2.2.2).1
    have hcomp := R.W_tgt (A.X.comp ψ' φ) (by rw [A.X.src_comp _ _ hs]; exact hW) c hc
      (by rw [A.X.tgt_comp _ _ hs]; exact ht)
    have hco : c ∈ R.o := hcomp.1
    have htψ' : A.X.tgt ψ' ∈ ⋃ y ∈ R.Y, R.N.U y := by
      have := hcomp.2
      rwa [A.X.tgt_comp _ _ hs] at this
    have hsψ' : A.X.src ψ' ∈ R.N.U (A.X.tgt ψ) := by rw [hs]; exact R.N.tgt_mem hψ hφψ
    obtain ⟨ω, hω, hψ'ω⟩ := R.N.exists_sheet_z5 ⟨mem_biUnion hψ.2 hsψ', htψ'⟩
    have hωs : A.X.src ω = A.X.tgt ψ := R.N.eq_of_mem_U_z5 hω.1 hψ.2 (R.N.src_mem hω hψ'ω) hsψ'
    have hωt : A.X.tgt ω ∈ closure (S.V c) := by
      by_contra hn
      exact Set.disjoint_left.1 (R.U_far _ hω.2 c hco hn) (R.N.tgt_mem hω hψ'ω)
        (subset_closure ht)
    have hωb : A.X.src ω ∈ closure (S.V b) := by rw [hωs]; exact hψt
    have hωψ := NaturalRepFinite.comp_mem_morOn (X := A.X) hψ hω hωs
    refine ⟨A.X.comp ω ψ, hωψ, by rw [A.X.src_comp _ _ hωs, hψs],
      by rw [A.X.tgt_comp _ _ hωs]; exact hωt, ?_, ?_⟩
    · have e := R.N.comp_srcInv_eq hψ hω hωs hφψ
      rw [← hs, R.N.srcInv_src hω hψ'ω] at e
      rw [e]
      refine R.N.srcInv_mem hωψ ?_
      rw [A.X.src_comp _ _ hωs]
      exact R.N.src_mem hψ hφψ
    · intro y hy
      have hyψ : y ∈ R.N.U (A.X.src ψ) := by rw [hψs]; exact hy.1
      have hφy : R.N.srcInv ψ y ∈ R.N.sheet ψ := R.N.srcInv_mem hψ hyψ
      have hsφy : A.X.src (R.N.srcInv ψ y) = y := R.N.src_srcInv hψ hyψ
      have htφy : A.X.tgt (R.N.srcInv ψ y) ∈ R.N.U (A.X.src ω) := by
        rw [hωs]; exact R.N.tgt_mem hψ hφy
      have hθ : R.N.srcInv ω (A.X.tgt (R.N.srcInv ψ y)) ∈ R.N.sheet ω := R.N.srcInv_mem hω htφy
      have hsθ : A.X.src (R.N.srcInv ω (A.X.tgt (R.N.srcInv ψ y))) =
          A.X.tgt (R.N.srcInv ψ y) := R.N.src_srcInv hω htφy
      have e := R.N.comp_srcInv_eq hψ hω hωs hφy
      rw [hsφy] at e
      rw [← e, A.X.tgt_comp _ _ hsθ]
      have htφyb : A.X.tgt (R.N.srcInv ψ y) ∈ A.X.PObj.boundary :=
        (tgt_mem_boundary_iff_z4 _).2 (by rw [hsφy]; exact hy.2)
      have hτ := R.tau_eq hω hb hco hωb hωt hθ hψ'ω
      have hθU : A.X.src (R.N.srcInv ω (A.X.tgt (R.N.srcInv ψ y))) ∈ (S.nbhd b).U :=
        (R.U_near _ hω.1 b hb hωb).1 (R.N.src_mem hω hθ)
      have hθU' : A.X.tgt (R.N.srcInv ω (A.X.tgt (R.N.srcInv ψ y))) ∈ (S.nbhd c).U :=
        (R.U_near _ hω.2 c hco hωt).1 (R.N.tgt_mem hω hθ)
      have e₂ := hD b hpr.2.1 c hc _ ⟨hθU, by rw [hsθ]; exact htφyb⟩ hθU' j k
        (by rw [hτ]; exact hp)
      rw [e₂, hsθ, htr y hy]
      have hao : a ∈ R.o := R.mem_o_of_mem_W hW hpr.1 hpr.2.2.1
      have hyU : y ∈ (S.nbhd a).U := (R.U_near z₀ R.mem_Y a hao hz₀).1 hy.1
      rw [fibAct_comp_p3w3 (by rw [D.P_s a hpr.1 i y ⟨hyU, hy.2⟩, hsφy]) hsθ]

/-- **The conclusion of the proof of Proposition 14.4.6 (2)**: if `(i, i') ∈ Θ_{z₀}` (a limit of
`z_k`-loops, `z_k ∈ V̂_a`) and `z₀ ∈ cl_X(V̂_a)`, then `s^{0a}_i = s^{0a}_{i'}` on `O(z₀) ∩ ∂X`. -/
theorem sections_eq (hD : D.CompatNbhd) {a : A.Obj} (ha : a ∈ S.A)
    (hz₀ : z₀ ∈ closure (S.V a)) {i i' : S.I a} (hθ : S.Theta a z₀ i i') :
    ∀ y ∈ R.N.U z₀ ∩ A.X.PObj.boundary, D.s a i y = D.s a i' y := by
  obtain ⟨z, hzW, hz⟩ := mem_closure_iff_nhds.1 hθ R.W R.W_mem
  obtain ⟨ψ, hψ, -, -, hzψ, htr⟩ :=
    R.arc_transport D hD (show S.Arc a a i i' (A.X.unit z) from hz)
      (by rw [A.X.src_unit]; exact hzW) hz₀
  have hu := NaturalRepFinite.unit_mem_morOn_z5 (X := A.X) R.mem_Y
  have hψ1 : ψ = A.X.unit z₀ :=
    R.N.eq_of_mem_sheet_z5 hψ hu hzψ (R.N.unit_mem_sheet_z5 R.mem_Y (R.W_subset hzW))
  subst hψ1
  intro y hy
  have e := htr y hy
  rw [R.N.srcInv_unit_z5 R.mem_Y hy.1, A.X.tgt_unit] at e
  have hao : a ∈ R.o := R.mem_o_of_mem_W hzW ha (ZSetup.ZRel.mem_V hz)
  have hyU : y ∈ (S.nbhd a).U := (R.U_near z₀ R.mem_Y a hao hz₀).1 hy.1
  rw [e, fibAct_unit_p3w3 (D.P_s a ha i y ⟨hyU, hy.2⟩)]

end ZLimitRep

end SBLocalization

end Polyfold
