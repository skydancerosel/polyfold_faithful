import Polyfold.Chapter13.P3G_GoodSystem
import Polyfold.Chapter7.NaturalRepFinite
import Polyfold.Chapter7.ProperSubsets

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
§14.4, pp. 661–662: **Lemma 14.4.7** (a finite collection of isomorphic objects; a restatement of
Proposition 7.1.15 and Corollary 7.1.17) (2017 text: Lemma 14.7).

# The natural representation of a finite set of isomorphic objects, as used in §14.4

## The text, paraphrased

For finitely many isomorphic objects `Y = {x₁, …, x_ℓ}` and open neighbourhoods `Q(x)` there is a
functorial construction: open connected `O(x) ⊆ Q(x)`, mutually disjoint, sc-diffeomorphisms
`f(ψ) : O(s(ψ)) → O(t(ψ))` with `f(ψ ∘ φ) = f(ψ) ∘ f(φ)`, `f(1_x) = id`; the morphisms between
points of `O = ⋃ O(x)` are the disjoint union of the components `𝐎(ψ)`, `ψ ∈ 𝐘`, and
(1) `G_x` acts on `O(x)` by the natural action, (2) `s, t : 𝐎(ψ) → O(s(ψ)), O(t(ψ))` are
sc-diffeomorphisms, (3) `f(ψ) = t ∘ (s|𝐎(ψ))⁻¹`, (4) `f(g)(z) = t(Γ(g, z)) = g ∗ z` for `g ∈ G_x`,
(5) `f(φ)(g ∗ z) = γ_φ(g) ∗ f(φ)(z)` with `γ_φ(g) = φ ∘ g ∘ φ⁻¹`, (6) the multiplication
`𝐎(ψ) ₛ×ₜ 𝐎(φ) → 𝐎(ψ ∘ φ)` is well defined and an sc-diffeomorphism, (7) every `O(x)` has the
properness property.

## What is formalized (namespace `Polyfold.EpGroupoid`)

Part II has Proposition 7.1.15 as `proposition_7_1_15_2017` (the structure `NaturalRepFinite Y V`
carries the open connected disjoint `U(y) ⊆ V`, the functor `F`, the components `𝐔(ψ)` and (1)–(3)).
Here:
* `exists_naturalRepFinite_subset`: the neighbourhoods inside the given `Q(x)` (one open set per
  object, not one common `V`) and with the properness property (7).
* `NaturalRepFinite.F_isotropy`: (4); `NaturalRepFinite.F_equivariant`: (5), with
  `γ_φ = conjIsotropy φ`.
* `NaturalRepFinite.comp_srcInv_eq`, `NaturalRepFinite.bijOn_comp`,
  `NaturalRepFinite.isScDiffeoOn_comp`:
  (6).  The fibre product `𝐔(ψ) ₛ×ₜ 𝐔(φ)` is parametrised by its second factor
  (`(ψ', φ') ↦ φ'`, inverse `φ' ↦ ((s|𝐔(ψ))⁻¹(t(φ')), φ')`); the multiplication is a bijection onto
  `𝐔(ψ ∘ φ)`, and in this parametrisation it is the sc-diffeomorphism
  `(s|𝐔(ψ ∘ φ))⁻¹ ∘ s : 𝐔(φ) → 𝐔(ψ ∘ φ)`.
* **Lemma 14.4.7**: `lemma_14_4_7`, all of the above for one natural representation.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

namespace NaturalRepFinite

variable {Y : Finset Obj} {V : Set Obj} (N : X.NaturalRepFinite Y V)

/-! ### Items (4) and (5) -/

/-- **Lemma 14.4.7 (4)**: for `g ∈ G_y`, `f(g)(z) = t(Γ(g, z)) = g ∗ z` with the natural action. -/
theorem F_isotropy {y : Obj} (hy : y ∈ Y) :
    ∃ R : X.NaturalRep y, R.U = N.U y ∧
      ∀ g, ∀ z ∈ N.U y, N.F g.val z = X.tgt (R.Γ g z) ∧ N.F g.val z = R.Φ g z := by
  obtain ⟨R, hRU, hR⟩ := N.natural y hy
  refine ⟨R, hRU, fun g z hz => ⟨?_, (hR g z hz).symm⟩⟩
  rw [← hR g z hz, R.tgt_Γ g z (hRU ▸ hz)]

theorem isotropy_mem_morOn {y : Obj} (hy : y ∈ Y) (g : X.Isotropy y) :
    g.val ∈ X.morOn (Y : Set Obj) :=
  ⟨by rw [g.src_val]; exact hy, by rw [g.tgt_val]; exact hy⟩

/-- **Lemma 14.4.7 (5)**: `f(φ)(g ∗ z) = γ_φ(g) ∗ f(φ)(z)` with `γ_φ(g) = φ ∘ g ∘ φ⁻¹`. -/
theorem F_equivariant {φ : Mor} (hφ : φ ∈ X.morOn (Y : Set Obj)) (g : X.Isotropy (X.src φ))
    {z : Obj} (hz : z ∈ N.U (X.src φ)) :
    N.F φ (N.F g.val z) = N.F (X.conjIsotropy φ g).val (N.F φ z) := by
  have hg := isotropy_mem_morOn hφ.1 g
  have hc := isotropy_mem_morOn hφ.2 (X.conjIsotropy φ g)
  have h₁ := N.F_comp φ hφ g.val hg g.tgt_val.symm z (by rw [g.src_val]; exact hz)
  have hcs : X.src (X.conjIsotropy φ g).val = X.tgt φ := (X.conjIsotropy φ g).src_val
  have h₂ := N.F_comp _ hc φ hφ hcs z hz
  rw [← h₁, ← h₂]
  congr 1
  have hφg : X.src (X.comp φ g.val) = X.src φ := by
    rw [X.src_comp _ _ g.tgt_val.symm, g.src_val]
  rw [conjIsotropy_val, X.comp_assoc _ _ _ (by rw [hφg, X.tgt_inv]) (X.src_inv φ), X.inv_comp,
    GroupoidStr.comp_unit_of_eq hφg]

/-! ### Item (6) -/

theorem srcInv_src {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) {ψ' : Mor} (h : ψ' ∈ N.sheet ψ) :
    N.srcInv ψ (X.src ψ') = ψ' :=
  (N.isScDiffeoOn_src ψ hψ).left_inv ψ' h

theorem src_mem {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) {ψ' : Mor} (h : ψ' ∈ N.sheet ψ) :
    X.src ψ' ∈ N.U (X.src ψ) :=
  (N.isScDiffeoOn_src ψ hψ).mapsTo h

theorem tgt_mem {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) {ψ' : Mor} (h : ψ' ∈ N.sheet ψ) :
    X.tgt ψ' ∈ N.U (X.tgt ψ) := by
  obtain ⟨τ, hτ⟩ := N.isScDiffeoOn_tgt ψ hψ
  exact hτ.mapsTo h

theorem srcInv_mem {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) {z : Obj}
    (hz : z ∈ N.U (X.src ψ)) : N.srcInv ψ z ∈ N.sheet ψ :=
  (N.isScDiffeoOn_src ψ hψ).mapsTo_inv hz

theorem src_srcInv {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) {z : Obj}
    (hz : z ∈ N.U (X.src ψ)) : X.src (N.srcInv ψ z) = z :=
  (N.isScDiffeoOn_src ψ hψ).right_inv z hz

theorem comp_mem_morOn {φ ψ : Mor} (hφ : φ ∈ X.morOn (Y : Set Obj))
    (hψ : ψ ∈ X.morOn (Y : Set Obj)) (h : X.src ψ = X.tgt φ) :
    X.comp ψ φ ∈ X.morOn (Y : Set Obj) :=
  ⟨by rw [X.src_comp _ _ h]; exact hφ.1, by rw [X.tgt_comp _ _ h]; exact hψ.2⟩

/-- **Lemma 14.4.7 (6), the key identity**: for `φ' ∈ 𝐔(φ)`, the composite
`(s|𝐔(ψ))⁻¹(t(φ')) ∘ φ'` is `(s|𝐔(ψ ∘ φ))⁻¹(s(φ'))`; in particular it lies in `𝐔(ψ ∘ φ)`
(a connectedness argument, the `𝐔(χ)` being the components of `𝐔`). -/
theorem comp_srcInv_eq {φ ψ : Mor} (hφ : φ ∈ X.morOn (Y : Set Obj))
    (hψ : ψ ∈ X.morOn (Y : Set Obj)) (h : X.src ψ = X.tgt φ) {φ' : Mor} (hφ' : φ' ∈ N.sheet φ) :
    X.comp (N.srcInv ψ (X.tgt φ')) φ' = N.srcInv (X.comp ψ φ) (X.src φ') := by
  have hψφ := comp_mem_morOn hφ hψ h
  let c : Mor → Mor := fun φ'' => X.comp (N.srcInv ψ (X.tgt φ'')) φ''
  have htU : ∀ φ'' ∈ N.sheet φ, X.tgt φ'' ∈ N.U (X.src ψ) := fun φ'' hφ'' => by
    rw [h]; exact N.tgt_mem hφ hφ''
  have hcomp : ∀ φ'' ∈ N.sheet φ, X.src (N.srcInv ψ (X.tgt φ'')) = X.tgt φ'' := fun φ'' hφ'' =>
    N.src_srcInv hψ (htU φ'' hφ'')
  have hcont : ContinuousOn c (N.sheet φ) :=
    continuousOn_comp_of_continuousOn
      ((N.isScDiffeoOn_src ψ hψ).isScSmoothOn_inv.continuousOn.comp
        X.continuous_tgt.continuousOn htU) continuousOn_id hcomp
  have hconn : IsConnected (c '' N.sheet φ) := (N.isConnected_sheet φ hφ).image c hcont
  have hsub : c '' N.sheet φ ⊆ X.morOn (⋃ y ∈ Y, N.U y) := by
    rintro _ ⟨φ'', hφ'', rfl⟩
    refine ⟨?_, ?_⟩
    · rw [X.src_comp _ _ (hcomp φ'' hφ'')]
      exact mem_biUnion hφ.1 (N.src_mem hφ hφ'')
    · rw [X.tgt_comp _ _ (hcomp φ'' hφ'')]
      exact mem_biUnion hψ.2 (N.tgt_mem hψ (N.srcInv_mem hψ (htU φ'' hφ'')))
  have hcφ : c φ = X.comp ψ φ := by
    change X.comp (N.srcInv ψ (X.tgt φ)) φ = X.comp ψ φ
    rw [← h, N.srcInv_src hψ (N.mem_sheet ψ hψ)]
  have hmem : X.comp ψ φ ∈ c '' N.sheet φ := ⟨φ, N.mem_sheet φ hφ, hcφ⟩
  have hin : c '' N.sheet φ ⊆ N.sheet (X.comp ψ φ) := by
    have := hconn.isPreconnected.subset_connectedComponentIn hmem hsub
    rwa [NatRepFinite.connectedComponentIn_morOn N hψφ (N.mem_sheet _ hψφ)] at this
  have hcφ' : X.comp (N.srcInv ψ (X.tgt φ')) φ' ∈ N.sheet (X.comp ψ φ) := hin ⟨φ', hφ', rfl⟩
  have e := N.srcInv_src hψφ hcφ'
  rw [X.src_comp _ _ (hcomp φ' hφ')] at e
  exact e.symm

/-- **Lemma 14.4.7 (6), well defined and bijective**: the multiplication
`m(ψ', φ') = ψ' ∘ φ'` maps the fibre product `𝐔(ψ) ₛ×ₜ 𝐔(φ)` bijectively onto `𝐔(ψ ∘ φ)`. -/
theorem bijOn_comp {φ ψ : Mor} (hφ : φ ∈ X.morOn (Y : Set Obj))
    (hψ : ψ ∈ X.morOn (Y : Set Obj)) (h : X.src ψ = X.tgt φ) :
    BijOn (fun p : Mor × Mor => X.comp p.1 p.2)
      {p | p.1 ∈ N.sheet ψ ∧ p.2 ∈ N.sheet φ ∧ X.src p.1 = X.tgt p.2}
      (N.sheet (X.comp ψ φ)) := by
  have hψφ := comp_mem_morOn hφ hψ h
  have hsrcψφ : X.src (X.comp ψ φ) = X.src φ := X.src_comp _ _ h
  -- `m(ψ', φ') = (s|𝐔(ψ ∘ φ))⁻¹(s(φ'))`
  have hm : ∀ p : Mor × Mor, p.1 ∈ N.sheet ψ → p.2 ∈ N.sheet φ → X.src p.1 = X.tgt p.2 →
      X.comp p.1 p.2 = N.srcInv (X.comp ψ φ) (X.src p.2) := by
    rintro ⟨ψ', φ'⟩ hψ' hφ' hs
    change X.comp ψ' φ' = _
    rw [← N.comp_srcInv_eq hφ hψ h hφ', ← hs, N.srcInv_src hψ hψ']
  have hsU : ∀ φ' ∈ N.sheet φ, X.src φ' ∈ N.U (X.src (X.comp ψ φ)) := fun φ' hφ' => by
    rw [hsrcψφ]; exact N.src_mem hφ hφ'
  refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_, fun χ hχ => ?_⟩
  · change X.comp p.1 p.2 ∈ _
    rw [hm p hp.1 hp.2.1 hp.2.2]
    exact N.srcInv_mem hψφ (hsU p.2 hp.2.1)
  · change X.comp p.1 p.2 = X.comp q.1 q.2 at hpq
    rw [hm p hp.1 hp.2.1 hp.2.2, hm q hq.1 hq.2.1 hq.2.2] at hpq
    have hs : X.src p.2 = X.src q.2 := by
      rw [← N.src_srcInv hψφ (hsU p.2 hp.2.1), hpq, N.src_srcInv hψφ (hsU q.2 hq.2.1)]
    have h2 : p.2 = q.2 := by
      rw [← N.srcInv_src hφ hp.2.1, ← N.srcInv_src hφ hq.2.1, hs]
    have h1 : p.1 = q.1 := by
      rw [← N.srcInv_src hψ hp.1, ← N.srcInv_src hψ hq.1, hp.2.2, hq.2.2, h2]
    exact Prod.ext h1 h2
  · have hχs : X.src χ ∈ N.U (X.src φ) := by
      rw [← hsrcψφ]; exact N.src_mem hψφ hχ
    set φ' := N.srcInv φ (X.src χ)
    have hφ' : φ' ∈ N.sheet φ := N.srcInv_mem hφ hχs
    have htU : X.tgt φ' ∈ N.U (X.src ψ) := by rw [h]; exact N.tgt_mem hφ hφ'
    refine ⟨(N.srcInv ψ (X.tgt φ'), φ'), ⟨N.srcInv_mem hψ htU, hφ', N.src_srcInv hψ htU⟩, ?_⟩
    change X.comp (N.srcInv ψ (X.tgt φ')) φ' = χ
    rw [N.comp_srcInv_eq hφ hψ h hφ', N.src_srcInv hφ hχs, N.srcInv_src hψφ hχ]

/-- **Lemma 14.4.7 (6), sc-diffeomorphism**: in the parametrisation of the fibre product by its
second factor, the multiplication is `(s|𝐔(ψ ∘ φ))⁻¹ ∘ s : 𝐔(φ) → 𝐔(ψ ∘ φ)`, an sc-diffeomorphism
(with inverse `(s|𝐔(φ))⁻¹ ∘ s`). -/
theorem isScDiffeoOn_comp {φ ψ : Mor} (hφ : φ ∈ X.morOn (Y : Set Obj))
    (hψ : ψ ∈ X.morOn (Y : Set Obj)) (h : X.src ψ = X.tgt φ) :
    (∀ φ' ∈ N.sheet φ, X.comp (N.srcInv ψ (X.tgt φ')) φ' =
      (N.srcInv (X.comp ψ φ) ∘ X.src) φ') ∧
    X.PMor.IsScDiffeoOn X.PMor (N.srcInv (X.comp ψ φ) ∘ X.src) (N.srcInv φ ∘ X.src)
      (N.sheet φ) (N.sheet (X.comp ψ φ)) := by
  refine ⟨fun φ' hφ' => N.comp_srcInv_eq hφ hψ h hφ', ?_⟩
  have hψφ := comp_mem_morOn hφ hψ h
  have h₂ := (N.isScDiffeoOn_src (X.comp ψ φ) hψφ).symm
  rw [X.src_comp _ _ h] at h₂
  exact h₂.comp (N.isScDiffeoOn_src φ hφ)

end NaturalRepFinite

/-! ### Item (7) and the neighbourhoods `Q(x)` -/

variable (X)

/-- **The neighbourhoods of Lemma 14.4.7 inside given `Q(x)`, with the properness property (7)**:
Proposition 7.1.15 applied to a union of pairwise disjoint small neighbourhoods. -/
theorem exists_naturalRepFinite_subset (Y : Finset Obj) (hY : ∀ y ∈ Y, ∀ y' ∈ Y, X.Isomorphic y y')
    (Q : Obj → Set Obj) (hQo : ∀ y ∈ Y, IsOpen (Q y)) (hQ : ∀ y ∈ Y, y ∈ Q y) :
    ∃ N : X.NaturalRepFinite Y (⋃ y ∈ Y, Q y),
      (∀ y ∈ Y, N.U y ⊆ Q y) ∧ ∀ y ∈ Y, X.IsProperSubset (closure (N.U y)) := by
  obtain ⟨W, hW, hdisj⟩ := (Y.finite_toSet).t2_separation
  choose P hyP hPo hPprop using fun y => X.exists_hasPropernessProperty y
  let G : Obj → Set Obj := fun y => W y ∩ Q y ∩ P y
  have hGo : ∀ y ∈ Y, IsOpen (G y) := fun y hy => ((hW y).2.inter (hQo y hy)).inter (hPo y)
  have hGW : ∀ y, G y ⊆ W y := fun y => inter_subset_left.trans inter_subset_left
  obtain ⟨N⟩ := X.proposition_7_1_15_2017 Y hY (isOpen_biUnion hGo)
    (fun y hy => mem_biUnion hy ⟨⟨(hW y).1, hQ y hy⟩, hyP y⟩)
  have hNG : ∀ y ∈ Y, N.U y ⊆ G y := by
    intro y hy
    refine (N.isConnected_U y hy).isPreconnected.subset_left_of_subset_union (hGo y hy)
      (v := ⋃ y' ∈ {y' | y' ∈ Y ∧ y' ≠ y}, G y') (isOpen_biUnion fun y' hy' => hGo y' hy'.1)
      (disjoint_iUnion₂_right.2 fun y' hy' =>
        ((hdisj (Finset.mem_coe.2 hy) (Finset.mem_coe.2 hy'.1) (Ne.symm hy'.2)).mono
          (hGW y) (hGW y')))
      (fun z hz => ?_) ⟨y, N.mem_U y hy, ⟨⟨(hW y).1, hQ y hy⟩, hyP y⟩⟩
    obtain ⟨y', hy', hz'⟩ := mem_iUnion₂.1 (N.U_subset y hy hz)
    by_cases hyy : y' = y
    · exact Or.inl (hyy ▸ hz')
    · exact Or.inr (mem_iUnion₂.2 ⟨y', ⟨hy', hyy⟩, hz'⟩)
  refine ⟨NatRepFinite.mono N (iUnion₂_mono fun y _ => inter_subset_left.trans inter_subset_right),
    fun y hy => (hNG y hy).trans (inter_subset_left.trans inter_subset_right), fun y hy => ?_⟩
  exact (hPprop y).of_subset (closure_mono ((hNG y hy).trans inter_subset_right)) isClosed_closure

/-- **Lemma 14.4.7, pp. 661–662 (2017: Lemma 14.7)** (restatement of Proposition 7.1.15 and
Corollary 7.1.17): for
finitely many isomorphic objects `Y` and open `Q(x) ∋ x` there is a natural representation of `Y`
(the structure `NaturalRepFinite`: open connected mutually disjoint `O(x)`, the functor `f`, the
components `𝐎(ψ)`, items (1)–(3)) with `O(x) ⊆ Q(x)` and (4) `f(g) = t ∘ Γ(g, ·) = g ∗ ·`,
(5) `f(φ)(g ∗ z) = γ_φ(g) ∗ f(φ)(z)`, (6) the multiplication `𝐎(ψ) ₛ×ₜ 𝐎(φ) → 𝐎(ψ ∘ φ)`
well defined and bijective, and an sc-diffeomorphism `𝐎(φ) → 𝐎(ψ ∘ φ)` in the parametrisation by
the second factor, (7) the properness property of every `O(x)`. -/
theorem lemma_14_4_7 (Y : Finset Obj) (hY : ∀ y ∈ Y, ∀ y' ∈ Y, X.Isomorphic y y')
    (Q : Obj → Set Obj) (hQo : ∀ y ∈ Y, IsOpen (Q y)) (hQ : ∀ y ∈ Y, y ∈ Q y) :
    ∃ N : X.NaturalRepFinite Y (⋃ y ∈ Y, Q y),
      (∀ y ∈ Y, N.U y ⊆ Q y) ∧
      (∀ y ∈ Y, ∃ R : X.NaturalRep y, R.U = N.U y ∧
        ∀ g, ∀ z ∈ N.U y, N.F g.val z = X.tgt (R.Γ g z) ∧ N.F g.val z = R.Φ g z) ∧
      (∀ φ ∈ X.morOn (Y : Set Obj), ∀ (g : X.Isotropy (X.src φ)), ∀ z ∈ N.U (X.src φ),
        N.F φ (N.F g.val z) = N.F (X.conjIsotropy φ g).val (N.F φ z)) ∧
      (∀ φ ∈ X.morOn (Y : Set Obj), ∀ ψ ∈ X.morOn (Y : Set Obj), X.src ψ = X.tgt φ →
        BijOn (fun p : Mor × Mor => X.comp p.1 p.2)
          {p | p.1 ∈ N.sheet ψ ∧ p.2 ∈ N.sheet φ ∧ X.src p.1 = X.tgt p.2}
          (N.sheet (X.comp ψ φ)) ∧
        (∀ φ' ∈ N.sheet φ, X.comp (N.srcInv ψ (X.tgt φ')) φ' =
          (N.srcInv (X.comp ψ φ) ∘ X.src) φ') ∧
        X.PMor.IsScDiffeoOn X.PMor (N.srcInv (X.comp ψ φ) ∘ X.src) (N.srcInv φ ∘ X.src)
          (N.sheet φ) (N.sheet (X.comp ψ φ))) ∧
      (∀ y ∈ Y, X.IsProperSubset (closure (N.U y))) := by
  obtain ⟨N, hNQ, hprop⟩ := X.exists_naturalRepFinite_subset Y hY Q hQo hQ
  exact ⟨N, hNQ, fun y hy => N.F_isotropy hy, fun φ hφ g z hz => N.F_equivariant hφ g hz,
    fun φ hφ ψ hψ h => ⟨N.bijOn_comp hφ hψ h, N.isScDiffeoOn_comp hφ hψ h⟩, hprop⟩

end EpGroupoid

end Polyfold
