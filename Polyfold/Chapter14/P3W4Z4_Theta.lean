import Polyfold.Chapter14.P3W4Z4_Deform

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
§14.4, pp. 663–664: **Definition 14.4.8** (`Θ_z` and `≈_z`) and **Lemma 14.4.9** (1), (2), (4)
(2017 text: Definition 14.8, Lemma 14.8), and the equivariant shrinking used for
Proposition 14.4.10.

# The relations `≈_z` on the closure of `V̂_a`

## The text, paraphrased

(Definition 14.4.8) For `a ∈ A` and `z ∈ cl_X(V̂_a)`, `Θ_z` is the set of pairs `(i, i')` for
which there are `z_k ∈ V̂_a` with `i ∼_{z_k} i'` and `z_k → z`; `i ≈_z i'` if a chain
`i = i₀, …, i_k = i'` with `(i_p, i_{p+1}) ∈ Θ_z` exists; `[i]_{≈_z}` is the class (14.44).
(Lemma 14.4.9) (1) `i ∼_z i'` implies `i ≈_z i'` for `z ∈ V̂_a`; (2) `i ≈_z i'` implies
`g(i) ≈_{g∗z} g(i')`, so `g([i]_{≈_z}) = [g(i)]_{≈_{g∗z}}`; (4) for `i ∈ I_a` and
`z₀ ∈ cl_X(V̂_a)` there is an open `Q̃(z₀) ⊆ Ũ(a)` with `[i]_{∼_z} ⊆ [i]_{≈_{z₀}}` for
`z ∈ V̂_a ∩ Q̃(z₀)`.  ((3) needs the section structures; it is in `P3W4Z4_Coherent`.)

## What is formalized

* `ZData.Theta a z i i'`: `z ∈ cl{y | i ∼_y i'}` (the sequences of the text read as the closure;
  `theta_iff_seq` shows they agree in a Fréchet–Urysohn space, e.g. a metrizable one).
  `ZData.Approx` (`≈_z`) is the reflexive–transitive closure of `Θ_z`, `approxClass` is
  `[i]_{≈_z}`; `approx_equivalence` (for `z ∈ cl_X(V̂_a)`, as the text calls it).
* `lemma_14_4_9_1`, `lemma_14_4_9_2`, `lemma_14_4_9_2_class`, `lemma_14_4_9_4`.
* `NatNbhd.exists_equivariant_nbhds`: open neighbourhoods `O(z)`, `z` in a `G_x`-invariant
  `C ⊆ U(x)`, with `O(g ∗ z) = g ∗ O(z)` and `O(z) ∩ O(g ∗ z) = ∅` when `g ∗ z ≠ z`, inside
  given neighbourhoods with a property preserved by shrinking and by the action (the step of
  Proposition 14.4.10 (2) that the text leaves to the reader).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

open SBLocalization

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-! ### The natural action on open sets -/

namespace NatNbhd

variable {x : Obj} (N : X.NatNbhd x)

theorem continuousAt_Φ (g : X.Isotropy x) {y : Obj} (hy : y ∈ N.U) :
    ContinuousAt (N.rep.Φ g) y :=
  (N.rep.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn.continuousAt
    (N.rep.isOpen_U.mem_nhds (N.U_subset hy))

/-- `g ∗ O = U ∩ Φ(g⁻¹)⁻¹(O)` for `O ⊆ U`. -/
theorem image_Φ_eq (g : X.Isotropy x) {O : Set Obj} (hO : O ⊆ N.U) :
    N.rep.Φ g '' O = N.U ∩ N.rep.Φ g⁻¹ ⁻¹' O := by
  ext y
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨N.mapsTo_Φ g (hO ho), by rw [mem_preimage, N.Φ_inv_Φ g (hO ho)]; exact ho⟩
  · rintro ⟨hy, hy'⟩
    refine ⟨_, hy', ?_⟩
    have := N.Φ_Φ_inv g hy
    exact this

theorem isOpen_image_Φ (g : X.Isotropy x) {O : Set Obj} (hO : O ⊆ N.U) (hOo : IsOpen O) :
    IsOpen (N.rep.Φ g '' O) := by
  rw [N.image_Φ_eq g hO]
  exact ((N.rep.isScDiffeoOn_Φ g⁻¹).isScSmoothOn.continuousOn.mono N.U_subset).isOpen_inter_preimage
    N.isOpen_U hOo

theorem image_Φ_subset (g : X.Isotropy x) {O : Set Obj} (hO : O ⊆ N.U) :
    N.rep.Φ g '' O ⊆ N.U := by
  rintro _ ⟨o, ho, rfl⟩
  exact N.mapsTo_Φ g (hO ho)

theorem image_Φ_mul (g h : X.Isotropy x) {O : Set Obj} (hO : O ⊆ N.U) :
    N.rep.Φ (g * h) '' O = N.rep.Φ g '' (N.rep.Φ h '' O) := by
  rw [image_image]
  exact image_congr fun y hy => N.Φ_mul g h (hO hy)

/-- **Equivariant shrinking** (the step behind Proposition 14.4.10 (2)): let `C ⊆ U(x)` be
`G_x`-invariant and `P z O` a property of neighbourhoods of `z ∈ C` that passes to smaller sets
and is carried along by the action, and assume every `z ∈ C` has an open `O ∋ z` with `P z O`.
Then there are open `O(z) ∋ z`, `O(z) ⊆ U(x)`, with `P z (O z)`, `O(g ∗ z) = g ∗ O(z)` and
`O(z) ∩ O(g ∗ z) = ∅` whenever `g ∗ z ≠ z`. -/
theorem exists_equivariant_nbhds {C : Set Obj} (hC : C ⊆ N.U)
    (hCinv : ∀ g, MapsTo (N.rep.Φ g) C C) (P : Obj → Set Obj → Prop)
    (hmono : ∀ z O O', P z O → O' ⊆ O → P z O')
    (hequiv : ∀ g z O, z ∈ C → O ⊆ N.U → P z O → P (N.rep.Φ g z) (N.rep.Φ g '' O))
    (hex : ∀ z ∈ C, ∃ O, IsOpen O ∧ z ∈ O ∧ P z O) :
    ∃ O : Obj → Set Obj, ∀ z ∈ C, IsOpen (O z) ∧ z ∈ O z ∧ O z ⊆ N.U ∧ P z (O z) ∧
      (∀ g, O (N.rep.Φ g z) = N.rep.Φ g '' O z) ∧
      ∀ g, N.rep.Φ g z ≠ z → Disjoint (O z) (O (N.rep.Φ g z)) := by
  have := X.proposition_7_1_12 x
  -- Step A: at each `w ∈ C` a stabiliser-invariant, separated neighbourhood
  have stepA : ∀ w ∈ C, ∃ O', IsOpen O' ∧ w ∈ O' ∧ O' ⊆ N.U ∧ P w O' ∧
      (∀ h, N.rep.Φ h w = w → MapsTo (N.rep.Φ h) O' O') ∧
      ∀ k, N.rep.Φ k w ≠ w → Disjoint O' (N.rep.Φ k '' O') := by
    intro w hw
    have hwU := hC hw
    obtain ⟨Q, hQo, hwQ, hPQ⟩ := hex w hw
    have hsep : ∀ k : X.Isotropy x, ∃ Pk Pk' : Set Obj, IsOpen Pk ∧ IsOpen Pk' ∧ w ∈ Pk ∧
        N.rep.Φ k w ∈ Pk' ∧ (N.rep.Φ k w ≠ w → Disjoint Pk Pk') := by
      intro k
      by_cases hk : N.rep.Φ k w = w
      · exact ⟨univ, univ, isOpen_univ, isOpen_univ, mem_univ _, mem_univ _, fun h => absurd hk h⟩
      · obtain ⟨Pk, Pk', ho, ho', hm, hm', hd⟩ := t2_separation (Ne.symm hk)
        exact ⟨Pk, Pk', ho, ho', hm, hm', fun _ => hd⟩
    choose Pk Pk' hPo hPo' hwP hwP' hsepP using hsep
    have hΦo : ∀ (k : X.Isotropy x) {S : Set Obj}, IsOpen S → IsOpen (N.U ∩ N.rep.Φ k ⁻¹' S) :=
      fun k _ hS => ((N.rep.isScDiffeoOn_Φ k).isScSmoothOn.continuousOn.mono
        N.U_subset).isOpen_inter_preimage N.isOpen_U hS
    let Q₁ : Set Obj := Q ∩ N.U ∩ ⋂ k, (Pk k ∩ (N.U ∩ N.rep.Φ k ⁻¹' Pk' k))
    have hQ₁o : IsOpen Q₁ :=
      (hQo.inter N.isOpen_U).inter (isOpen_iInter_of_finite fun k => (hPo k).inter (hΦo k (hPo' k)))
    have hwQ₁ : w ∈ Q₁ := ⟨⟨hwQ, hwU⟩, mem_iInter.2 fun k => ⟨hwP k, hwU, hwP' k⟩⟩
    let stab : Set (X.Isotropy x) := {h | N.rep.Φ h w = w}
    let O' : Set Obj := ⋂ h ∈ stab, (N.U ∩ N.rep.Φ h ⁻¹' Q₁)
    have h1 : (1 : X.Isotropy x) ∈ stab := N.Φ_one hwU
    have hO'Q₁ : O' ⊆ Q₁ := fun y hy => by
      have := mem_iInter₂.1 hy 1 h1
      have h' := this.2
      rwa [mem_preimage, N.Φ_one this.1] at h'
    have hO'U : O' ⊆ N.U := fun y hy => (hO'Q₁ hy).1.2
    refine ⟨O', (toFinite stab).isOpen_biInter fun h _ => hΦo h hQ₁o,
      mem_iInter₂.2 fun h hh => ⟨hwU, by rw [mem_preimage, hh]; exact hwQ₁⟩, hO'U,
      hmono w Q O' hPQ fun y hy => (hO'Q₁ hy).1.1, ?_, ?_⟩
    · intro h' hh' y hy
      have hyU := hO'U hy
      refine mem_iInter₂.2 fun h hh => ⟨N.mapsTo_Φ h' hyU, ?_⟩
      rw [mem_preimage, ← N.Φ_mul h h' hyU]
      have hhh : h * h' ∈ stab := by
        change N.rep.Φ (h * h') w = w
        rw [N.Φ_mul h h' hwU, hh', hh]
      exact (mem_iInter₂.1 hy (h * h') hhh).2
    · intro k hk
      rw [Set.disjoint_left]
      rintro y hy ⟨y', hy', rfl⟩
      have h₁ : N.rep.Φ k y' ∈ Pk' k := ((mem_iInter.1 (hO'Q₁ hy').2 k).2).2
      have h₂ : N.rep.Φ k y' ∈ Pk k := (mem_iInter.1 (hO'Q₁ hy).2 k).1
      exact Set.disjoint_left.1 (hsepP k hk) h₂ h₁
  -- Step B: transport from orbit representatives
  choose! O' hO'o hwO' hO'U hPO' hO'stab hO'sep using stepA
  have : Nonempty Obj := ⟨x⟩
  let orb : Obj → Set Obj := fun z => range fun g => N.rep.Φ g z
  let r : Obj → Obj := fun z => Classical.epsilon (· ∈ orb z)
  have horb : ∀ z ∈ C, ∀ g, orb (N.rep.Φ g z) = orb z := by
    intro z hz g
    ext w
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h * g, N.Φ_mul h g (hC hz)⟩
    · rintro ⟨h, rfl⟩
      refine ⟨h * g⁻¹, ?_⟩
      change N.rep.Φ (h * g⁻¹) (N.rep.Φ g z) = N.rep.Φ h z
      rw [N.Φ_mul h g⁻¹ (N.mapsTo_Φ g (hC hz)), N.Φ_inv_Φ g (hC hz)]
  have hr : ∀ z ∈ C, ∃ h, N.rep.Φ h (r z) = z := by
    intro z hz
    obtain ⟨g, hg⟩ : r z ∈ orb z :=
      Classical.epsilon_spec (p := (· ∈ orb z)) ⟨z, 1, N.Φ_one (hC hz)⟩
    refine ⟨g⁻¹, ?_⟩
    rw [← hg, N.Φ_inv_Φ g (hC hz)]
  have hrC : ∀ z ∈ C, r z ∈ C := by
    intro z hz
    obtain ⟨g, hg⟩ : r z ∈ orb z :=
      Classical.epsilon_spec (p := (· ∈ orb z)) ⟨z, 1, N.Φ_one (hC hz)⟩
    rw [← hg]; exact hCinv g hz
  have hrΦ : ∀ z ∈ C, ∀ g, r (N.rep.Φ g z) = r z := by
    intro z hz g
    change Classical.epsilon (· ∈ orb (N.rep.Φ g z)) = Classical.epsilon (· ∈ orb z)
    rw [horb z hz g]
  choose! hz hhz using hr
  let O : Obj → Set Obj := fun z => N.rep.Φ (hz z) '' O' (r z)
  have wd : ∀ z ∈ C, ∀ k, N.rep.Φ k (r z) = z → O z = N.rep.Φ k '' O' (r z) := by
    intro z hzC k hk
    have hrz := hrC z hzC
    have hrzU := hC hrz
    have hU := hO'U (r z) hrz
    set m := (hz z)⁻¹ * k
    have hm : N.rep.Φ m (r z) = r z := by
      have e := N.Φ_inv_Φ (hz z) hrzU
      rw [hhz z hzC] at e
      rw [N.Φ_mul _ _ hrzU, hk, e]
    have hm' : N.rep.Φ m⁻¹ (r z) = r z := by
      conv_lhs => rw [← hm]
      exact N.Φ_inv_Φ m hrzU
    have himg : N.rep.Φ m '' O' (r z) = O' (r z) := by
      refine (hO'stab _ hrz m hm).image_subset.antisymm fun y hy => ?_
      exact ⟨_, hO'stab _ hrz _ hm' hy, N.Φ_Φ_inv m (hU hy)⟩
    have hk' : k = hz z * m := by simp [m]
    change N.rep.Φ (hz z) '' O' (r z) = _
    rw [hk', N.image_Φ_mul _ _ hU, himg]
  have heq : ∀ z ∈ C, ∀ g, O (N.rep.Φ g z) = N.rep.Φ g '' O z := by
    intro z hzC g
    have hgz := hCinv g hzC
    have hU := hO'U (r z) (hrC z hzC)
    rw [wd _ hgz (g * hz z) (by rw [hrΦ z hzC, N.Φ_mul _ _ (hC (hrC z hzC)), hhz z hzC]),
      hrΦ z hzC, N.image_Φ_mul _ _ hU]
  refine ⟨O, fun z hzC => ?_⟩
  have hrz := hrC z hzC
  have hrzU := hC hrz
  have hU := hO'U (r z) hrz
  refine ⟨N.isOpen_image_Φ _ hU (hO'o _ hrz), ⟨r z, hwO' _ hrz, hhz z hzC⟩,
    N.image_Φ_subset _ hU, ?_, heq z hzC, ?_⟩
  · have := hequiv (hz z) (r z) _ hrz hU (hPO' _ hrz)
    rwa [hhz z hzC] at this
  · intro g hg
    rw [heq z hzC g, Set.disjoint_left]
    rintro y ⟨y₁, hy₁, rfl⟩ ⟨y', ⟨y₂, hy₂, rfl⟩, hy⟩
    set k := (hz z)⁻¹ * g * hz z
    have hy₁U := hU hy₁
    have hy₂U := hU hy₂
    have hk : N.rep.Φ k y₂ = y₁ := by
      have e : N.rep.Φ g (N.rep.Φ (hz z) y₂) = N.rep.Φ (hz z) y₁ := hy
      rw [N.Φ_mul _ _ hy₂U, N.Φ_mul _ _ (N.mapsTo_Φ _ hy₂U), e, N.Φ_inv_Φ _ hy₁U]
    have hkr : N.rep.Φ k (r z) ≠ r z := by
      intro hkr
      apply hg
      have e : hz z * k = g * hz z := by simp [k, mul_assoc]
      calc N.rep.Φ g z = N.rep.Φ g (N.rep.Φ (hz z) (r z)) := by rw [hhz z hzC]
        _ = N.rep.Φ (g * hz z) (r z) := (N.Φ_mul _ _ hrzU).symm
        _ = N.rep.Φ (hz z * k) (r z) := by rw [e]
        _ = z := by rw [N.Φ_mul _ _ hrzU, hkr, hhz z hzC]
    exact Set.disjoint_left.1 (hO'sep _ hrz k hkr) hy₁ ⟨y₂, hy₂, hk⟩

end NatNbhd

/-! ### Definition 14.4.8: `Θ_z` and `≈_z` -/

namespace ZData

variable (S : X.ZData)

/-- **Definition 14.4.8, p. 663 (2017: Definition 14.8), `Θ_z`**: `(i, i') ∈ Θ_z` if
`z ∈ cl{y | i ∼_y i'}`, i.e. there are `z_k ∈ V̂_a` with `i ∼_{z_k} i'` and `z_k → z` (the
sequences of the text read as the closure; `theta_iff_seq`). -/
def Theta (a z : Obj) (i i' : S.I a) : Prop := z ∈ closure {y | S.ZRel a y i i'}

/-- **Definition 14.4.8, `≈_z`**: `i ≈_z i'` if there is a chain `i = i₀, …, i_k = i'` with
`(i_p, i_{p+1}) ∈ Θ_z`. -/
def Approx (a z : Obj) : S.I a → S.I a → Prop := Relation.ReflTransGen (S.Theta a z)

/-- **(14.44)**: `[i]_{≈_z} = {i' ∈ I_a | i' ≈_z i}`. -/
def approxClass (a z : Obj) (i : S.I a) : Set (S.I a) := {i' | S.Approx a z i' i}

variable {S}

/-- With sequences: in a Fréchet–Urysohn space (for instance a metrizable one) `Θ_z` is the
text's set of limits of sequences. -/
theorem theta_iff_seq [FrechetUrysohnSpace Obj] {a z : Obj} {i i' : S.I a} :
    S.Theta a z i i' ↔ ∃ zk : ℕ → Obj, (∀ k, S.ZRel a (zk k) i i') ∧ Tendsto zk atTop (𝓝 z) :=
  mem_closure_iff_seq_limit

theorem ZRel.symm' {a z : Obj} {i i' : S.I a} (h : S.ZRel a z i i') : S.ZRel a z i' i :=
  (S.zRel_equivalence (ZSetup.Arc.props h).1 h.mem_V).symm h

theorem theta_symm {a z : Obj} {i i' : S.I a} (h : S.Theta a z i i') : S.Theta a z i' i :=
  closure_mono (fun _ hy => ZRel.symm' hy) h

theorem theta_subset_closure {a z : Obj} {i i' : S.I a} (h : S.Theta a z i i') :
    z ∈ closure (S.V a) :=
  closure_mono (fun _ hy => ZSetup.ZRel.mem_V hy) h

theorem approx_symm {a z : Obj} {i i' : S.I a} (h : S.Approx a z i i') : S.Approx a z i' i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (theta_symm hbc) ih

/-- `≈_z` is an equivalence relation on `I_a` (as the text calls it, for `z ∈ cl_X(V̂_a)`). -/
theorem approx_equivalence {a z : Obj} :
    Equivalence (S.Approx a z) where
  refl _ := Relation.ReflTransGen.refl
  symm h := approx_symm h
  trans h₁ h₂ := h₁.trans h₂

/-- Each `(i, i)` lies in `Θ_z` for `z ∈ cl_X(V̂_a)`. -/
theorem theta_refl {a z : Obj} (ha : a ∈ S.A) (hz : z ∈ closure (S.V a)) (i : S.I a) :
    S.Theta a z i i :=
  closure_mono (fun _ hy => ZSetup.Arc.nil ha hy i) hz

/-! ### Lemma 14.4.9 -/

/-- **Lemma 14.4.9 (1), p. 663 (2017: Lemma 14.8 (1))**: `i ∼_z i'` implies `i ≈_z i'`. -/
theorem lemma_14_4_9_1 {a z : Obj} {i i' : S.I a} (h : S.ZRel a z i i') : S.Approx a z i i' :=
  Relation.ReflTransGen.single (subset_closure h)

theorem theta_smul {a z : Obj} {i i' : S.I a} (h : S.Theta a z i i') (g : X.Isotropy a) :
    S.Theta a ((S.nbhd a).rep.Φ g z) (g • i) (g • i') := by
  have ha : a ∈ S.A := by
    obtain ⟨_, hy⟩ := mem_closure_iff_nhds.1 h univ univ_mem
    exact (ZSetup.Arc.props hy.2).1
  have hzU : z ∈ (S.nbhd a).U := S.closure_V_subset a ha (theta_subset_closure h)
  refine closure_mono ?_ (mem_closure_image ((S.nbhd a).continuousAt_Φ g hzU) h)
  rintro _ ⟨y, hy, rfl⟩
  exact (S.lemma_14_4_5 ha hy.mem_V g i i').1 hy

/-- **Lemma 14.4.9 (2), p. 663 (2017: Lemma 14.8 (2))**: `i ≈_z i'` implies
`g(i) ≈_{g∗z} g(i')`. -/
theorem lemma_14_4_9_2 {a z : Obj} {i i' : S.I a} (h : S.Approx a z i i') (g : X.Isotropy a) :
    S.Approx a ((S.nbhd a).rep.Φ g z) (g • i) (g • i') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (theta_smul hbc g)

/-- **Lemma 14.4.9 (2), the classes**: `[g(i)]_{≈_{g∗z}} = g([i]_{≈_z})` for `z ∈ cl_X(V̂_a)`. -/
theorem lemma_14_4_9_2_class {a z : Obj} (ha : a ∈ S.A) (hz : z ∈ closure (S.V a))
    (g : X.Isotropy a) (i : S.I a) :
    S.approxClass a ((S.nbhd a).rep.Φ g z) (g • i) = (g • ·) '' S.approxClass a z i := by
  have hzU : z ∈ (S.nbhd a).U := S.closure_V_subset a ha hz
  ext j
  constructor
  · intro hj
    refine ⟨g⁻¹ • j, ?_, smul_inv_smul g j⟩
    have := lemma_14_4_9_2 hj g⁻¹
    rwa [(S.nbhd a).Φ_inv_Φ g hzU, inv_smul_smul] at this
  · rintro ⟨j', hj', rfl⟩
    exact lemma_14_4_9_2 hj' g

/-- **Lemma 14.4.9 (4), p. 664 (2017: Lemma 14.8 (4))**: for `i ∈ I_a` and `z₀ ∈ cl_X(V̂_a)`
there is an open `Q̃(z₀) ∋ z₀` in `Ũ(a)` with `[i]_{∼_z} ⊆ [i]_{≈_{z₀}}` for
`z ∈ V̂_a ∩ Q̃(z₀)`. -/
theorem lemma_14_4_9_4 {a z₀ : Obj} (ha : a ∈ S.A) (hz₀ : z₀ ∈ closure (S.V a)) (i : S.I a) :
    ∃ Q : Set Obj, IsOpen Q ∧ z₀ ∈ Q ∧ Q ⊆ (S.nbhd a).U ∧
      ∀ z ∈ S.V a ∩ Q, S.zClass a z i ⊆ S.approxClass a z₀ i := by
  let bad : Set (S.I a) := {i' | ¬ S.Approx a z₀ i' i}
  refine ⟨(S.nbhd a).U ∩ ⋂ i' ∈ bad, (closure {y | S.ZRel a y i' i})ᶜ,
    (S.nbhd a).isOpen_U.inter ((toFinite bad).isOpen_biInter fun _ _ =>
      isClosed_closure.isOpen_compl),
    ⟨S.closure_V_subset a ha hz₀,
      mem_iInter₂.2 fun i' hi' h => hi' (Relation.ReflTransGen.single h)⟩,
    inter_subset_left, ?_⟩
  rintro z ⟨-, -, hzQ⟩ i' hi'
  by_contra hbad
  exact mem_iInter₂.1 hzQ i' hbad (subset_closure hi')

/-- Lemma 14.4.9 (4) for all `i` at once (`I_a` is finite). -/
theorem lemma_14_4_9_4_all {a z₀ : Obj} (ha : a ∈ S.A) (hz₀ : z₀ ∈ closure (S.V a)) :
    ∃ Q : Set Obj, IsOpen Q ∧ z₀ ∈ Q ∧ Q ⊆ (S.nbhd a).U ∧
      ∀ z ∈ S.V a ∩ Q, ∀ i, S.zClass a z i ⊆ S.approxClass a z₀ i := by
  choose Q hQo hzQ hQU hQ using fun i => lemma_14_4_9_4 ha hz₀ i
  exact ⟨(S.nbhd a).U ∩ ⋂ i, Q i, (S.nbhd a).isOpen_U.inter (isOpen_iInter_of_finite hQo),
    ⟨S.closure_V_subset a ha hz₀, mem_iInter.2 hzQ⟩, inter_subset_left, fun z hz i =>
      hQ i z ⟨hz.1, mem_iInter.1 hz.2.2 i⟩⟩

end ZData

end EpGroupoid

end Polyfold
