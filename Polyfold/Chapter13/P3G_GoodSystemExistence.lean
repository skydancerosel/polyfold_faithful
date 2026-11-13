import Polyfold.Chapter13.P3G_GoodSystem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), Part III, §13.1, pp. 602–606:
**Theorem 13.1.7** (extension of good partial systems, p. 602) and **Theorem 13.1.8** (existence
of good systems, p. 604).  (2017 text: Theorem 13.1, Theorem 13.2.)

# Existence of good systems of neighbourhoods

## The text, paraphrased

(Theorem 13.1.7) Let `Q` be an open subset of the object space with `|Q| = |Y|`, and let
`(U(q))_{q ∈ Q}` be a good system for the full subcategory on `Q`.  Then for arbitrary open
`W(y) ∋ y`, `y ∉ Q`, there are open `U(y) ⊆ W(y)` such that `(U(y))_{y ∈ Y}` is a good system.
*Proof*: for `y ∉ Q` pick `ψ_y : q_y → y` with `q_y ∈ Q` and a sheet `O(ψ_y)` with
`s(O(ψ_y)) ⊆ U(q_y)`, `U(y) = t(O(ψ_y))` small; then the components of `𝒰(q, y)`, `𝒰(y, q)`,
`𝒰(y, z)` are carried into components of `𝒰(q, q_y)`, `𝒰(q_y, z)`, `𝒰(q_y, q_z)` by
`φ ↦ [(t|O(ψ_y))⁻¹(t φ)]⁻¹ ∘ φ`, `φ ↦ φ⁻¹`, `φ ↦ [(t|O(ψ_z))⁻¹(t φ)]⁻¹ ∘ φ ∘ (t|O(ψ_y))⁻¹(s φ)`.
(Theorem 13.1.8) If `|X|` is paracompact, then for every family of open `W(x) ∋ x` there is a good
system with `U(x) ⊆ W(x)` "for all `∈ X`".  *Proof*: shrink `W(x)` to have the natural action and
proper closure; take a locally finite refinement `(Ṽ_x)` of `(|W(x)|)` with `cl Ṽ_x ⊆ |W(x)|`
(Theorem 7.3.1); `V_a = π⁻¹(Ṽ_a) ∩ W(a)`, `cl V_a ⊆ W(a)` (Lemma 13.1.1), `V = ⋃ V_a` with
`|V| = |X|`; for `x ∈ V` the set `Θ_x` of morphisms from `cl V` to `x` is finite, and a small
invariant `U(x)` makes the morphisms from `cl V` into `U(x)` lie in a disjoint union of sheets
around `Θ_x`; this gives a good system on `V`, which Theorem 13.1.7 extends.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **Transport of condition (3)**: `IsTransport σ U V` (a continuous section `σ` of `t` over `U`
  with `s ∘ σ` injective into `V`), `isTransport_unit`; `injOn_comp_of_transport`: if `U, U'`
  have transports into `V, V'` and the components of `𝒰(V, V')` satisfy condition (3), so do
  those of `𝒰(U, U')` (the maps `A`, `C` of the proof of Theorem 13.1.7 in one form).
* **Small target neighbourhoods**: `exists_nhds_injOn_of_isProperSubset` (for finitely many
  closed proper `A_i` and a point `y`, an open `V ∋ y` such that `s` and `t` are injective on
  every preconnected set of morphisms from `⋃ A_i` into `V`: the step with `Θ_x` of the proof of
  Theorem 13.1.8).
* **Theorem 13.1.7**: `theorem_13_1_7` (with `exists_transport_of_isGoodOn`).
* **Theorem 13.1.8**: `theorem_13_1_8`.

## Reading

* **Theorem 13.1.7: "a good system for the ep-groupoid `Q`"** is `IsGoodOn N Q`: `U(q) ⊆ Q` for
  `q ∈ Q`, the natural actions and condition (3) as in `X` (they coincide for the full
  subcategory on the open `Q`), and condition (1) read in `X`: `t : s⁻¹(cl_X U(q)) → X` proper.
  This is the form the proof uses ("`U` clearly satisfies Properties (1) and (2)"); the project
  has no full sub-ep-groupoid on an open non-saturated `Q`.  The good system extends the given
  family (`𝒰.nbhd q = N q` for `q ∈ Q`).
* **The proof of Theorem 13.1.7** is organised differently: every `x` gets a transport (the
  units for `x ∈ Q`, `(t|O(ψ_x))⁻¹` otherwise) and one argument covers the text's three cases;
  the text's extra smallness condition on `U(y)` (the components of `𝒰(q_y, y)`) is not needed.
* **Theorem 13.1.8**: "for all `∈ X`" is read as "for all `x ∈ X`" (presumably a dropped
  symbol).  The paracompactness of `|X|` enters through `precise_refinement` and the shrinking
  lemma (normality of the paracompact Hausdorff `|X|`, Lemma 7.3.4); the text's metrizability is
  not needed.  The text's conditions (6), (7) on `U₀(x)` are replaced by
  `exists_nhds_injOn_of_isProperSubset` applied to the finitely many `cl V_a` near `|x|`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Transport of condition (3) -/

/-- **A transport of `U` into `V`**: a continuous section `σ` of `t` over `U` (`t(σ z) = z`) with
`s ∘ σ` injective on `U` and mapping `U` into `V`.  (For `y ∉ Q` in Theorem 13.1.7 this is
`(t|O(ψ_y))⁻¹`; for `q ∈ Q` the units.) -/
structure IsTransport (σ : Obj → Mor) (U V : Set Obj) : Prop where
  continuousOn : ContinuousOn σ U
  tgt_eq : ∀ z ∈ U, X.tgt (σ z) = z
  mapsTo : MapsTo (fun z => X.src (σ z)) U V
  injOn : InjOn (fun z => X.src (σ z)) U

/-- The units transport `U` into itself. -/
theorem isTransport_unit (U : Set Obj) : X.IsTransport X.unit U U where
  continuousOn := X.continuous_unit.continuousOn
  tgt_eq z _ := X.tgt_unit z
  mapsTo z hz := by simp only [X.src_unit]; exact hz
  injOn a _ b _ h := by simpa only [X.src_unit] using h

variable {X}

/-- **Transport of condition (3)** (the three cases of the proof of Theorem 13.1.7): if `σ`
transports `U` into `V`, `σ'` transports `U'` into `V'`, and `s, t` are injective on the
connected components of `𝒰(V, V')`, then they are injective on the connected components of
`𝒰(U, U')`.  The components are carried by `φ ↦ σ'(t φ)⁻¹ ∘ φ ∘ σ(s φ)`. -/
theorem injOn_comp_of_transport {U U' V V' : Set Obj} {σ σ' : Obj → Mor}
    (hσ : X.IsTransport σ U V) (hσ' : X.IsTransport σ' U' V')
    (hV : ∀ φ ∈ X.morBetween V V', InjOn X.src (connectedComponentIn (X.morBetween V V') φ) ∧
      InjOn X.tgt (connectedComponentIn (X.morBetween V V') φ))
    {φ₀ : Mor} (hφ₀ : φ₀ ∈ X.morBetween U U') :
    InjOn X.src (connectedComponentIn (X.morBetween U U') φ₀) ∧
      InjOn X.tgt (connectedComponentIn (X.morBetween U U') φ₀) := by
  set M := X.morBetween U U'
  set F : Mor → Mor := fun φ => X.comp (X.inv (σ' (X.tgt φ))) (X.comp φ (σ (X.src φ)))
  -- composability on `M`
  have h₁ : ∀ φ ∈ M, X.src φ = X.tgt (σ (X.src φ)) := fun φ hφ => (hσ.tgt_eq _ hφ.1).symm
  have h₂ : ∀ φ ∈ M, X.src (X.inv (σ' (X.tgt φ))) = X.tgt (X.comp φ (σ (X.src φ))) :=
    fun φ hφ => by rw [X.src_inv, hσ'.tgt_eq _ hφ.2, X.tgt_comp _ _ (h₁ φ hφ)]
  have hsF : ∀ φ ∈ M, X.src (F φ) = X.src (σ (X.src φ)) := fun φ hφ => by
    simp only [F]
    rw [X.src_comp _ _ (h₂ φ hφ), X.src_comp _ _ (h₁ φ hφ)]
  have htF : ∀ φ ∈ M, X.tgt (F φ) = X.src (σ' (X.tgt φ)) := fun φ hφ => by
    simp only [F]
    rw [X.tgt_comp _ _ (h₂ φ hφ), X.tgt_inv]
  have hFM : MapsTo F M (X.morBetween V V') := fun φ hφ =>
    ⟨by rw [hsF φ hφ]; exact hσ.mapsTo hφ.1, by rw [htF φ hφ]; exact hσ'.mapsTo hφ.2⟩
  -- continuity of `F` on `M`
  have hcF : ContinuousOn F M := by
    have ha : ContinuousOn (fun φ => σ (X.src φ)) M :=
      hσ.continuousOn.comp X.continuous_src.continuousOn fun φ hφ => hφ.1
    have hb : ContinuousOn (fun φ => X.inv (σ' (X.tgt φ))) M :=
      X.continuous_inv.comp_continuousOn
        (hσ'.continuousOn.comp X.continuous_tgt.continuousOn fun φ hφ => hφ.2)
    exact continuousOn_comp_of_continuousOn hb
      (continuousOn_comp_of_continuousOn continuousOn_id ha h₁) h₂
  -- `F` carries the component of `φ₀` into the component of `F φ₀`
  set C := connectedComponentIn M φ₀
  have hCM : C ⊆ M := connectedComponentIn_subset _ _
  have hFC : F '' C ⊆ connectedComponentIn (X.morBetween V V') (F φ₀) :=
    (isPreconnected_connectedComponentIn.image F (hcF.mono hCM)).subset_connectedComponentIn
      ⟨φ₀, mem_connectedComponentIn hφ₀, rfl⟩ (image_subset_iff.2 (hFM.mono_left hCM))
  obtain ⟨hinjs, hinjt⟩ := hV (F φ₀) (hFM hφ₀)
  -- cancellation
  have hcancel : ∀ φ₁ ∈ M, ∀ φ₂ ∈ M, X.src φ₁ = X.src φ₂ → X.tgt φ₁ = X.tgt φ₂ →
      F φ₁ = F φ₂ → φ₁ = φ₂ := by
    intro φ₁ hφ₁ φ₂ hφ₂ hs ht hF
    simp only [F] at hF
    rw [hs, ht] at hF
    have hc₁ := h₂ φ₁ hφ₁
    rw [ht, hs] at hc₁
    have hc₂ := h₂ φ₂ hφ₂
    have e := GroupoidStr.comp_left_cancel (G := X.toGroupoidStr) hc₁ hc₂ hF
    have hd₁ : X.src φ₁ = X.tgt (σ (X.src φ₂)) := by
      rw [hσ.tgt_eq _ hφ₂.1]
      exact hs
    exact GroupoidStr.comp_right_cancel (G := X.toGroupoidStr) hd₁ (h₁ φ₂ hφ₂) e
  have hmemF : ∀ φ ∈ C, F φ ∈ connectedComponentIn (X.morBetween V V') (F φ₀) :=
    fun φ hφ => hFC (mem_image_of_mem F hφ)
  refine ⟨fun φ₁ hφ₁ φ₂ hφ₂ hs => ?_, fun φ₁ hφ₁ φ₂ hφ₂ ht => ?_⟩
  · have hFe : F φ₁ = F φ₂ := hinjs (hmemF φ₁ hφ₁) (hmemF φ₂ hφ₂) (by
      rw [hsF φ₁ (hCM hφ₁), hsF φ₂ (hCM hφ₂), hs])
    have ht : X.tgt φ₁ = X.tgt φ₂ := hσ'.injOn (hCM hφ₁).2 (hCM hφ₂).2 (by
      change X.src (σ' (X.tgt φ₁)) = X.src (σ' (X.tgt φ₂))
      rw [← htF φ₁ (hCM hφ₁), ← htF φ₂ (hCM hφ₂), hFe])
    exact hcancel φ₁ (hCM hφ₁) φ₂ (hCM hφ₂) hs ht hFe
  · have hFe : F φ₁ = F φ₂ := hinjt (hmemF φ₁ hφ₁) (hmemF φ₂ hφ₂) (by
      rw [htF φ₁ (hCM hφ₁), htF φ₂ (hCM hφ₂), ht])
    have hs : X.src φ₁ = X.src φ₂ := hσ.injOn (hCM hφ₁).1 (hCM hφ₂).1 (by
      change X.src (σ (X.src φ₁)) = X.src (σ (X.src φ₂))
      rw [← hsF φ₁ (hCM hφ₁), ← hsF φ₂ (hCM hφ₂), hFe])
    exact hcancel φ₁ (hCM hφ₁) φ₂ (hCM hφ₂) hs ht hFe

/-! ### Small target neighbourhoods -/

/-- Every morphism lies in an open set on which `s` and `t` are injective (a sheet). -/
theorem exists_isOpen_injOn_src_tgt (φ : Mor) :
    ∃ O : Set Mor, IsOpen O ∧ φ ∈ O ∧ InjOn X.src O ∧ InjOn X.tgt O := by
  obtain ⟨W₁, V₁, σ₁, h₁, hd₁⟩ := X.isLocalScDiffeo_src φ
  obtain ⟨W₂, V₂, σ₂, h₂, hd₂⟩ := X.isLocalScDiffeo_tgt φ
  exact ⟨W₁ ∩ W₂, hd₁.isOpen_source.inter hd₂.isOpen_source, ⟨h₁, h₂⟩,
    hd₁.injOn.mono inter_subset_left, hd₂.injOn.mono inter_subset_right⟩

/-- **The step with `Θ_x` of the proof of Theorem 13.1.8**: for finitely many closed sets `A_i`
with the properness property and a point `y`, there is an open `V ∋ y` such that `s` and `t` are
injective on every preconnected set of morphisms with source in `⋃ A_i` and target in `V`.  (The
finitely many morphisms `Θ` from `⋃ A_i` to `y` get disjoint sheets; by properness all morphisms
from `⋃ A_i` into a small `V` lie in these sheets.) -/
theorem exists_nhds_injOn_of_isProperSubset {ι : Type*} (F : Finset ι) (A : ι → Set Obj)
    (hAc : ∀ i ∈ F, IsClosed (A i)) (hA : ∀ i ∈ F, X.IsProperSubset (A i)) (y : Obj) :
    ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ ∀ C ⊆ X.morBetween (⋃ i ∈ F, A i) V,
      IsPreconnected C → InjOn X.src C ∧ InjOn X.tgt C := by
  set Θ : Set Mor := {φ | X.src φ ∈ ⋃ i ∈ F, A i ∧ X.tgt φ = y}
  have hΘ : Θ.Finite := by
    refine (F.finite_toSet.biUnion fun i hi =>
      finite_setOf_of_isProperMap_domRestrict (hA i hi)
        X.isLocalScDiffeo_tgt.isLocalHomeomorph.isLocallyInjective y).subset ?_
    rintro φ ⟨hs, ht⟩
    obtain ⟨i, hi, hφ⟩ := mem_iUnion₂.1 hs
    exact mem_iUnion₂.2 ⟨i, hi, hφ, ht⟩
  choose O hOo hφO hOs hOt using fun φ : Mor => X.exists_isOpen_injOn_src_tgt φ
  obtain ⟨S, hS, hSdisj⟩ := hΘ.t2_separation
  set O' : Mor → Set Mor := fun φ => O φ ∩ S φ
  have hO'o : ∀ φ, IsOpen (O' φ) := fun φ => (hOo φ).inter (hS φ).2
  set Ω := ⋃ φ ∈ Θ, O' φ
  have hΩo : IsOpen Ω := isOpen_biUnion fun φ _ => hO'o φ
  -- the closed sets `t(s⁻¹(A_i) ∖ Ω)` miss `y`
  set B : ι → Set Obj := fun i => X.tgt '' (X.src ⁻¹' A i ∩ Ωᶜ)
  have hBc : ∀ i ∈ F, IsClosed (B i) := fun i hi =>
    isClosed_image_of_isProperMap_domRestrict (hA i hi) inter_subset_left
      (((hAc i hi).preimage X.continuous_src).inter hΩo.isClosed_compl)
  have hyB : ∀ i ∈ F, y ∉ B i := by
    rintro i hi ⟨φ, ⟨hφA, hφΩ⟩, rfl⟩
    exact hφΩ (mem_biUnion (x := φ) ⟨mem_iUnion₂.2 ⟨i, hi, hφA⟩, rfl⟩ ⟨hφO φ, (hS φ).1⟩)
  refine ⟨⋂ i ∈ F, (B i)ᶜ, isOpen_biInter_finset fun i hi => (hBc i hi).isOpen_compl,
    mem_iInter₂.2 hyB, fun C hC hCc => ?_⟩
  -- every morphism from `⋃ A_i` into `V` lies in `Ω`
  have hCΩ : C ⊆ Ω := fun φ hφ => by
    by_contra hφΩ
    obtain ⟨i, hi, hφA⟩ := mem_iUnion₂.1 (hC hφ).1
    exact (mem_iInter₂.1 (hC hφ).2 i hi) ⟨φ, ⟨hφA, hφΩ⟩, rfl⟩
  rcases C.eq_empty_or_nonempty with rfl | ⟨φ₀, hφ₀⟩
  · exact ⟨injOn_empty _, injOn_empty _⟩
  obtain ⟨θ, hθ, hφ₀θ⟩ := mem_iUnion₂.1 (hCΩ hφ₀)
  have hsub : C ⊆ O' θ := by
    refine hCc.subset_left_of_subset_union (hO'o θ)
      (isOpen_biUnion (s := Θ \ {θ}) fun φ _ => hO'o φ) ?_ ?_ ⟨φ₀, hφ₀, hφ₀θ⟩
    · refine disjoint_iUnion₂_right.2 fun φ hφ => ?_
      exact ((hSdisj hθ hφ.1 (Ne.symm hφ.2)).mono inter_subset_right inter_subset_right)
    · intro ψ hψ
      obtain ⟨φ, hφ, hψφ⟩ := mem_iUnion₂.1 (hCΩ hψ)
      by_cases h : φ = θ
      · exact Or.inl (h ▸ hψφ)
      · exact Or.inr (mem_iUnion₂.2 ⟨φ, ⟨hφ, h⟩, hψφ⟩)
  exact ⟨(hOs θ).mono (hsub.trans inter_subset_left), (hOt θ).mono (hsub.trans inter_subset_left)⟩

/-! ### Theorem 13.1.7 -/

variable (X)

/-- **The neighbourhoods of the proof of Theorem 13.1.7**: every `x` has a neighbourhood `U(x)`
with the natural action and the properness property and a transport of `U(x)` into some `U(q)`,
`q ∈ Q`: for `x ∈ Q` the given `U(x)` with the units, for `x ∉ Q` a small `U(x) ⊆ W(x)` inside
`t(O(ψ_x))` with `(t|O(ψ_x))⁻¹`, where `ψ_x : q → x` and `s(O(ψ_x)) ⊆ U(q)`. -/
theorem exists_transport_of_isGoodOn {Q : Set Obj} (hπQ : X.π '' Q = univ)
    (N : ∀ x : Obj, X.NatNbhd x) (hN : X.IsGoodOn N Q) (W : Obj → Set Obj)
    (hW : ∀ y, IsOpen (W y)) (hyW : ∀ y, y ∈ W y) (x : Obj) :
    ∃ (q : Obj) (M : X.NatNbhd x) (σ : Obj → Mor), q ∈ Q ∧ X.IsProperSubset (closure M.U) ∧
      X.IsTransport σ M.U (N q).U ∧ (x ∈ Q → M = N x) ∧ (x ∉ Q → M.U ⊆ W x) := by
  by_cases hx : x ∈ Q
  · exact ⟨x, N x, X.unit, hx, hN.isProperSubset_closure x hx, X.isTransport_unit _,
      fun _ => rfl, fun h => (h hx).elim⟩
  -- a morphism `ψ : q → x` with `q ∈ Q`
  obtain ⟨q, hq, hqx⟩ : X.π x ∈ X.π '' Q := hπQ ▸ mem_univ _
  obtain ⟨ψ, rfl, hψt⟩ := (X.π_eq_π_iff).1 hqx
  -- a sheet `O(ψ)` with `s(O(ψ)) ⊆ U(q)`
  obtain ⟨O₀, hO₀o, hψO₀, hO₀s, hO₀t⟩ := X.exists_isOpen_injOn_src_tgt ψ
  set O := O₀ ∩ X.src ⁻¹' (N (X.src ψ)).U
  have hOo : IsOpen O := hO₀o.inter ((N _).isOpen_U.preimage X.continuous_src)
  have hψO : ψ ∈ O := ⟨hψO₀, (N _).mem_U⟩
  have : Nonempty Mor := ⟨ψ⟩
  have hd := X.isLocalScDiffeo_tgt.isScDiffeoOn_invFunOn hOo (hO₀t.mono inter_subset_left)
  have hTo : IsOpen (X.tgt '' O) := hd.isOpen_target
  have hxT : x ∈ X.tgt '' O := ⟨ψ, hψO, hψt⟩
  obtain ⟨M, hMsub, hMp⟩ := X.exists_natNbhd_isProperSubset x ((hW x).inter hTo) ⟨hyW x, hxT⟩
  refine ⟨X.src ψ, M, Function.invFunOn X.tgt O, hq, hMp, ?_, fun h => (hx h).elim,
    fun _ => fun z hz => (hMsub hz).1⟩
  have hMT : M.U ⊆ X.tgt '' O := fun z hz => (hMsub hz).2
  exact
    { continuousOn := hd.isScSmoothOn_inv.continuousOn.mono hMT
      tgt_eq := fun z hz => hd.right_inv z (hMT hz)
      mapsTo := fun z hz => (hd.mapsTo_inv (hMT hz)).2
      injOn := fun a ha b hb h => by
        have e := (hO₀s.mono inter_subset_left) (hd.mapsTo_inv (hMT ha)) (hd.mapsTo_inv (hMT hb))
          h
        rw [← hd.right_inv a (hMT ha), ← hd.right_inv b (hMT hb), e] }

/-- **Theorem 13.1.7 (extension of good partial systems, p. 602; 2017: Theorem 13.1)**: let
`Q ⊆ X` be open with `|Q| = |X|` and `(U(q))_{q ∈ Q}` a good system on `Q` (`IsGoodOn N Q`).
For open neighbourhoods `W(y)`, `y ∉ Q`, there is a good system `𝒰` of `X` extending the given
one (`𝒰.nbhd q = N q` for `q ∈ Q`) with `U(y) ⊆ W(y)` for `y ∉ Q`. -/
theorem theorem_13_1_7 {Q : Set Obj} (hπQ : X.π '' Q = univ) (N : ∀ x : Obj, X.NatNbhd x)
    (hN : X.IsGoodOn N Q) (W : Obj → Set Obj) (hW : ∀ y, IsOpen (W y)) (hyW : ∀ y, y ∈ W y) :
    ∃ 𝒰 : X.GoodSystem, (∀ q ∈ Q, 𝒰.nbhd q = N q) ∧ ∀ y ∉ Q, 𝒰.U y ⊆ W y := by
  choose q M σ hq hMp hσ hMQ hMW using X.exists_transport_of_isGoodOn hπQ N hN W hW hyW
  have hgood : X.IsGoodOn M univ := by
    refine ⟨fun _ _ => subset_univ _, fun x _ => hMp x, fun x _ x' _ φ hφ => ?_⟩
    refine (isDiffeoComponent_iff_injOn
      (isOpen_connectedComponentIn_mor X (isOpen_morBetween (M x).isOpen_U (M x').isOpen_U) φ)).2
      (injOn_comp_of_transport (hσ x) (hσ x') (fun ψ hψ => ?_) hφ)
    have h := hN.isDiffeoComponent (q x) (hq x) (q x') (hq x') ψ hψ
    exact ⟨h.injOn_src, h.injOn_tgt⟩
  exact ⟨GoodSystem.ofIsGoodOn M hgood, fun q' hq' => hMQ q' hq', fun y hy => hMW y hy⟩

/-! ### Theorem 13.1.8 -/

/-- **Theorem 13.1.8 (existence of good systems, p. 604; 2017: Theorem 13.2)**: if the orbit
space `|X|` is paracompact, then for every family of open neighbourhoods `W(x) ∋ x` there is a
good system of open neighbourhoods `(U(x))` with `U(x) ⊆ W(x)` for all `x ∈ X`. -/
theorem theorem_13_1_8 (hX : X.HasParacompactOrbitSpace) (W : Obj → Set Obj)
    (hW : ∀ x, IsOpen (W x)) (hxW : ∀ x, x ∈ W x) :
    ∃ 𝒰 : X.GoodSystem, ∀ x, 𝒰.U x ⊆ W x := by
  have : ParacompactSpace X.OrbitSpace := hX
  -- (1), (2): neighbourhoods `W'(x) ⊆ W(x)` with the natural action and proper closure
  choose N₀ hN₀W hN₀p using fun x => X.exists_natNbhd_isProperSubset x (hW x) (hxW x)
  -- a locally finite refinement `Ṽ_a` of `(|W'(a)|)` with `cl Ṽ_a ⊆ |W'(a)|`
  obtain ⟨v, hvo, hvU, hvlf, hvsub⟩ := precise_refinement (fun x => X.π '' (N₀ x).U)
    (fun x => X.proposition_7_1_8 _ (N₀ x).isOpen_U) (iUnion_eq_univ_iff.2 fun z => by
      obtain ⟨x, rfl⟩ := X.surjective_π z
      exact ⟨x, mem_image_of_mem _ (N₀ x).mem_U⟩)
  obtain ⟨v', hv'U, hv'o, hv'cl⟩ := exists_subset_iUnion_closure_subset isClosed_univ hvo
    (fun z _ => hvlf.point_finite z) (by rw [hvU])
  have hcllf : LocallyFinite fun a => closure (v' a) := hvlf.subset hv'cl
  -- `V_a = π⁻¹(Ṽ_a) ∩ W'(a)` and `V = ⋃ V_a`
  set Va : Obj → Set Obj := fun a => X.π ⁻¹' v' a ∩ (N₀ a).U
  have hVao : ∀ a, IsOpen (Va a) := fun a =>
    ((hv'o a).preimage X.continuous_π).inter (N₀ a).isOpen_U
  have hValf : LocallyFinite Va :=
    (hcllf.preimage_continuous X.continuous_π).subset fun a y hy => subset_closure hy.1
  have hVacl : ∀ a, closure (Va a) ⊆ (N₀ a).U := fun a =>
    (X.lemma_13_1_1 (N₀ a) (hN₀p a) inter_subset_right).2
      ((closure_mono (image_subset_iff.2 fun y hy => hy.1)).trans ((hv'cl a).trans (hvsub a)))
  set V := ⋃ a, Va a
  have hVo : IsOpen V := isOpen_iUnion hVao
  have hπV : X.π '' V = univ := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨a, ha⟩ := mem_iUnion.1 (hv'U (mem_univ z))
    obtain ⟨w, hw, rfl⟩ := hvsub a (hv'cl a (subset_closure ha))
    exact ⟨w, mem_iUnion.2 ⟨a, ha, hw⟩, rfl⟩
  have hclV : closure V = ⋃ a, closure (Va a) := hValf.closure_iUnion
  have hVap : ∀ a, X.IsProperSubset (closure (Va a)) := fun a =>
    isProperMap_domRestrict_of_subset_of_isClosed X.continuous_src (hN₀p a)
      ((hVacl a).trans subset_closure) isClosed_closure
  -- near every `x`, only finitely many `cl V_a` matter
  have hloc : ∀ x : Obj, ∃ (G : Set Obj) (F : Finset Obj), IsOpen G ∧ x ∈ G ∧
      ∀ φ, X.src φ ∈ closure V → X.tgt φ ∈ G → ∃ a ∈ F, X.src φ ∈ closure (Va a) := by
    intro x
    obtain ⟨t, ht, hfin⟩ := hcllf (X.π x)
    obtain ⟨Ñ, hÑt, hÑo, hxÑ⟩ := mem_nhds_iff.1 ht
    refine ⟨X.π ⁻¹' Ñ, hfin.toFinset, hÑo.preimage X.continuous_π, hxÑ, fun φ hs ht' => ?_⟩
    rw [hclV] at hs
    obtain ⟨a, ha⟩ := mem_iUnion.1 hs
    refine ⟨a, hfin.mem_toFinset.2 ⟨X.π (X.src φ), ?_, hÑt ?_⟩, ha⟩
    · have h1 : X.π (X.src φ) ∈ closure (X.π '' Va a) :=
        image_closure_subset_closure_image X.continuous_π (mem_image_of_mem _ ha)
      exact closure_mono (image_subset_iff.2 fun y hy => hy.1) h1
    · rw [X.π_src_eq_π_tgt]
      exact ht'
  -- the neighbourhoods `U(x)`, `x ∈ V`
  have hnb : ∀ x : Obj, ∃ M : X.NatNbhd x, M.U ⊆ W x ∧ X.IsProperSubset (closure M.U) ∧
      (x ∈ V → M.U ⊆ V ∧ ∀ C ⊆ X.morBetween (closure V) M.U, IsPreconnected C →
        InjOn X.src C ∧ InjOn X.tgt C) := by
    intro x
    by_cases hx : x ∈ V
    · obtain ⟨G, F, hGo, hxG, hG⟩ := hloc x
      obtain ⟨V', hV'o, hxV', hV'⟩ := X.exists_nhds_injOn_of_isProperSubset F
        (fun a => closure (Va a)) (fun _ _ => isClosed_closure) (fun a _ => hVap a) x
      obtain ⟨M, -, hMsub⟩ := (N₀ x).exists_restrict_subset ((hVo.inter hGo).inter hV'o)
        ⟨⟨hx, hxG⟩, hxV'⟩
      refine ⟨M, fun z hz => hN₀W x (hMsub hz).1,
        isProperMap_domRestrict_of_subset_of_isClosed X.continuous_src (hN₀p x)
          (closure_mono fun z hz => (hMsub hz).1) isClosed_closure,
        fun _ => ⟨fun z hz => (hMsub hz).2.1.1, fun C hC hCc => hV' C ?_ hCc⟩⟩
      intro φ hφ
      obtain ⟨a, ha, hφa⟩ := hG φ (hC hφ).1 (hMsub (hC hφ).2).2.1.2
      exact ⟨mem_iUnion₂.2 ⟨a, ha, hφa⟩, (hMsub (hC hφ).2).2.2⟩
    · exact ⟨N₀ x, hN₀W x, hN₀p x, fun h => (hx h).elim⟩
  choose N₁ hN₁W hN₁p hN₁V using hnb
  -- a good system on `V`
  have hgood : X.IsGoodOn N₁ V := by
    refine ⟨fun q hq => (hN₁V q hq).1, fun q _ => hN₁p q, fun q hq q' hq' φ hφ => ?_⟩
    refine (isDiffeoComponent_iff_injOn (isOpen_connectedComponentIn_mor X
      (isOpen_morBetween (N₁ q).isOpen_U (N₁ q').isOpen_U) φ)).2
      ((hN₁V q' hq').2 _ ?_ isPreconnected_connectedComponentIn)
    intro ψ hψ
    have hψ' := connectedComponentIn_subset _ _ hψ
    exact ⟨subset_closure ((hN₁V q hq).1 hψ'.1), hψ'.2⟩
  -- extend by Theorem 13.1.7
  obtain ⟨𝒰, h𝒰Q, h𝒰W⟩ := X.theorem_13_1_7 hπV N₁ hgood W hW hxW
  refine ⟨𝒰, fun x => ?_⟩
  by_cases hx : x ∈ V
  · change (𝒰.nbhd x).U ⊆ W x
    rw [h𝒰Q x hx]
    exact hN₁W x
  · exact h𝒰W x hx

/-! ### Satisfiability -/

/-- **Good systems exist** (nonvacuity of Definition 13.1.2): the trivial ep-groupoid of every
M-polyfold has paracompact orbit space, so Theorem 13.1.8 gives a good system inside any
neighbourhoods. -/
theorem nonempty_goodSystem_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] (P : MPolyfold Z) : Nonempty (trivial P).GoodSystem := by
  obtain ⟨𝒰, -⟩ := (trivial P).theorem_13_1_8 (hasParacompactOrbitSpace_trivial P)
    (fun _ => univ) (fun _ => isOpen_univ) (fun _ => mem_univ _)
  exact ⟨𝒰⟩

end EpGroupoid

end Polyfold
