import Polyfold.Chapter14.P3W5FM_BoundaryPush
import Polyfold.Chapter3.FredholmPullbackIso
import Polyfold.Chapter3.RestrictOpenGerms
import Polyfold.Chapter10.FredholmEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.1, Proposition 14.1.8,
p. 645 (2017: Proposition 14.1): **condition (1) of Definition 14.1.3 is invariant under local
strong bundle isomorphisms**, which removes the hypothesis `PullMap.FacePull_hyp` of
`P3W5FM_BoundaryPull`.

## The text, paraphrased

(p. 646) The proof of Proposition 14.1.8 carries the local sc⁺-structures over `∂X` along a
representative of a generalized strong bundle isomorphism "by an argument similar to" Theorems
13.4.1 and 13.4.3; that the sections stay sc⁺ on every face is taken for granted.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IsScPlusOnFaceNear.of_restrict_p6`: a face germ on a smaller retract `O₁ = O ∩ N` (`N` open)
  of a smaller `K₁ ⊆ K`, with the same representative on `O₁ ∩ {tᵢ = 0}`, is one on `O`.
* `isFaceScPlusSectionOn_iff_singleton`: (1) of Definition 14.1.3 is pointwise.
* `isFaceScPlusSectionOn_of_localIso`: **the key lemma**.  For a local strong bundle isomorphism
  `L : W|U → W'|U'` (Part I's `LocalIso`), if `s = Ψ ∘ s' ∘ ϕ` on `G ∩ ∂X` (`G ⊆ U` open around
  `x ∈ ∂X`) and `s'` has (1) at `ϕ(x)`, then `s` has (1) at `x`.  Proof: a tame chart `c` at
  `x` is restricted to `dom φ ∩ G` (`StrongBundleChart.restrictInter`, tame by
  `IsTameChart.restrictInter`) and transported along `L⁻¹` (`LocalIso.transportChart`, a tame
  chart of `W'` with the same model, `isTameChart_transportChart`); the local representative of
  `s'` there is that of `s` in `c` on the face points (which lie in `∂X`,
  `symm_mem_boundary_fm`).
* `PullMap.facePull_hyp`: **FM's hypothesis `FacePull_hyp` holds for every `PullMap`** (strong
  bundle equivalences, proper strong bundle coverings).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open TameBoundary

/-! ### Face germs on a smaller retract -/

section Local

variable {E F W : ScBanach} {n : ℕ}

/-- A face germ for `(O₁, K₁, s₁)` gives one for `(O, K, s)` when `O ∩ N ⊆ O₁ ⊆ O` for an open
`N ∋ x`, `K₁ ⊆ K`, and `s₁ = s` on `O₁ ∩ {tᵢ = 0}`. -/
theorem IsScPlusOnFaceNear.of_restrict_p6 {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}
    {C O O₁ : Set (E 0)} {K K₁ : Set (E 0 × F 0)} {s s₁ : E 0 → E 0 × F 1} {x : E 0}
    {i : Fin n} (h : IsScPlusOnFaceNear T C O₁ K₁ s₁ x i) (hO₁ : O₁ ⊆ O) {N : Set (E 0)}
    (hN : IsOpen N) (hxN : x ∈ N) (hON : O ∩ N ⊆ O₁) (hK : K₁ ⊆ K)
    (hss : EqOn s₁ s (O₁ ∩ coordHyper T i)) : IsScPlusOnFaceNear T C O K s x i := by
  obtain ⟨V, hV, hxV, hret, hsec⟩ := h
  have hset : O ∩ (V ∩ N) ∩ coordHyper T i = (O₁ ∩ V ∩ coordHyper T i) ∩ N := by
    ext z
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨⟨hzO, hzV, hzN⟩, hzH⟩
      exact ⟨⟨⟨hON ⟨hzO, hzN⟩, hzV⟩, hzH⟩, hzN⟩
    · rintro ⟨⟨⟨hz1, hzV⟩, hzH⟩, hzN⟩
      exact ⟨⟨hO₁ hz1, hzV, hzN⟩, hzH⟩
  refine ⟨V ∩ N, hV.inter hN, ⟨hxV, hxN⟩, ?_, ?_⟩
  · rw [hset]; exact proposition_2_3_1_one hret hN
  · rw [hset]
    have h1 := hsec.isScSmooth.restrict hret (W := N)
    refine ⟨fun z hz => ?_, ?_⟩
    · rw [← hss ⟨hz.1.1.1, hz.1.2⟩]; exact hsec.fst_eq z hz.1
    · exact (h1.mono_target (h1.mapsTo.mono_right (strongShiftOne_mono hK))).congr
        fun z hz => hss ⟨hz.1.1.1, hz.1.2⟩

end Local

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A C : SEP.{u}}

/-! ### (1) of Definition 14.1.3 is pointwise -/

/-- (1) of Definition 14.1.3 on `D` is (1) at every point of `D`. -/
theorem isFaceScPlusSectionOn_iff_singleton {s : A.Obj → A.W} {D : Set A.Obj} :
    IsFaceScPlusSectionOn A s D ↔ ∀ x ∈ D, IsFaceScPlusSectionOn A s {x} := by
  constructor
  · intro h x hx
    exact h.mono (singleton_subset_iff.2 hx)
  · intro h
    refine ⟨fun x hx => (h x hx).1 x rfl, fun c hc n W T hT x hx i hi => ?_⟩
    exact (h x hx.1).2 c hc n W T hT x ⟨rfl, hx.2⟩ i hi

/-! ### The key lemma -/

/-- **(1) of Definition 14.1.3 is carried along local strong bundle isomorphisms.**  For
`L : W|U → W'|U'`, an open `G ⊆ U` around `x ∈ ∂X` with `s = Ψ ∘ s' ∘ ϕ` on `G ∩ ∂X`: if `s'`
has (1) at `ϕ(x)` (in every tame strong bundle chart of `W'`), then `s` has (1) at `x` (in every
tame strong bundle chart of `W`).  The chart of `W` at `x` is restricted into `G` and transported
along `L⁻¹` to a tame chart of `W'` with the same model. -/
theorem isFaceScPlusSectionOn_of_localIso {U : Set C.Obj} {U' : Set A.Obj}
    (L : LocalIso C.B A.B U U') {s : C.Obj → C.W} {s' : A.Obj → A.W} {x : C.Obj}
    {G : Set C.Obj} (hG : IsOpen G) (hxG : x ∈ G) (hGU : G ⊆ U)
    (hx : x ∈ C.X.PObj.boundary) (heq : EqOn s (L.Ψ ∘ s' ∘ L.ϕ) (G ∩ C.X.PObj.boundary))
    (hs' : IsFaceScPlusSectionOn A s' {L.ϕ x}) : IsFaceScPlusSectionOn C s {x} := by
  have hxU : x ∈ U := hGU hxG
  have hϕx : L.ϕ x ∈ U' := L.base.mapsTo hxU
  have hsx : s x = L.Ψ (s' (L.ϕ x)) := heq ⟨hxG, hx⟩
  obtain ⟨hP', h1'⟩ := hs'.1 (L.ϕ x) rfl
  have hPU' : A.P (s' (L.ϕ x)) ∈ U' := by rw [hP']; exact hϕx
  refine ⟨fun y hy => ?_, fun c hc n W T hT y hy i hi => ?_⟩
  · rw [mem_singleton_iff.1 hy, hsx]
    refine ⟨?_, L.mem_oneSet_Ψ hPU' h1'⟩
    rw [L.covers_inv _ hPU', hP', L.base.left_inv x hxU]
  have hyx : y = x := hy.1
  have hcx : x ∈ c.φ.source := hyx ▸ hy.2
  rw [hyx] at hi ⊢
  -- the restricted chart `c₁ = c|dom φ ∩ G` and the transported chart `c' = c₁ ∘ L⁻¹`
  have hc₁ : C.B.IsTameChart (c.restrictInter hG) := hc.restrictInter hG
  have hsub : (c.restrictInter hG).φ.source ⊆ U := fun z hz => hGU hz.2
  have hc' : A.B.IsTameChart (L.symm.transportChart (c.restrictInter hG) hsub) :=
    L.symm.isTameChart_transportChart _ hsub hc₁
  have hϕxc' : L.ϕ x ∈ (L.symm.transportChart (c.restrictInter hG) hsub).φ.source := by
    refine ⟨hϕx, ?_⟩
    change L.g (L.ϕ x) ∈ c.φ.source ∩ G
    rw [L.base.left_inv x hxU]
    exact ⟨hcx, hxG⟩
  have hc'x : (L.symm.transportChart (c.restrictInter hG) hsub).φ (L.ϕ x) = c.φ x := by
    change c.φ (L.g (L.ϕ x)) = c.φ x
    rw [L.base.left_inv x hxU]
  have hface := hs'.2 _ hc' n W T hT (L.ϕ x) ⟨rfl, hϕxc'⟩ i (by rw [hc'x]; exact hi)
  rw [hc'x] at hface
  -- the retract of `c'` is `φ(dom φ ∩ G) = O ∩ N`
  have hso : IsOpen (c.φ.source ∩ G) := c.φ.isOpen_source.inter hG
  have hO₁ : (L.symm.transportChart (c.restrictInter hG) hsub).φ.model.O =
      c.φ '' (c.φ.source ∩ G) :=
    L.symm.transportChart_model_O _ hsub
  have hON : c.φ '' (c.φ.source ∩ G) =
      c.φ.model.O ∩ c.restrictOpen (s := c.φ.source ∩ G) inter_subset_left hso :=
    c.image_eq_restrictOpen _ _
  refine hface.of_restrict_p6 (O := c.φ.model.O) (K := c.K) (s := localRepOne c s) ?_
    (c.isOpen_restrictOpen (s := c.φ.source ∩ G) inter_subset_left hso) ?_ ?_ ?_ ?_
  · rw [hO₁, hON]; exact inter_subset_left
  · have : c.φ x ∈ c.φ '' (c.φ.source ∩ G) := ⟨x, ⟨hcx, hxG⟩, rfl⟩
    rw [hON] at this; exact this.2
  · rw [hO₁, hON]
  · exact Set.image_mono (prod_mono (c.restrictInter_U_subset hG) subset_rfl)
  · rintro z ⟨hz, hzH⟩
    rw [hO₁] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hzO : c.φ w ∈ c.φ.model.O := c.φ.mapsTo_model w hw.1
    have hsymm : c.φ.symm (c.φ w) = w := c.φ.symm_apply_apply hw.1
    have hbd : w ∈ C.X.PObj.boundary := by
      have := symm_mem_boundary_fm c hc hT hzO (i := i) hzH
      rwa [hsymm] at this
    change localRepOne c (L.Ψ ∘ s' ∘ L.ϕ) (c.φ w) = localRepOne c s (c.φ w)
    unfold localRepOne
    rw [hsymm, heq ⟨hw.2, hbd⟩]

/-! ### `FacePull_hyp` holds -/

namespace PullMap

/-- **FM's hypothesis `FacePull_hyp` holds for every pull-back map** (strong bundle equivalences,
`PullMap.ofEquivalence`; proper strong bundle coverings, `PullMap.ofCovering`): near every `x` the
pulled-back section is `Ψ ∘ s' ∘ F` for the local strong bundle isomorphism of `Φ` at `x`. -/
theorem facePull_hyp (M : PullMap C A) : M.FacePull_hyp := by
  intro s' O O' hO hO' hOO' hs'
  refine isFaceScPlusSectionOn_iff_singleton.2 fun x hx => ?_
  obtain ⟨U₀, U₀', hxU₀, hi⟩ := M.isLocalIso x
  have hG : IsOpen (U₀ ∩ O) := hi.toLocalIso.isOpen_U.inter hO
  refine isFaceScPlusSectionOn_of_localIso hi.toLocalIso hG ⟨hxU₀, hx.1⟩ inter_subset_left hx.2
    ?_ (hs'.mono (singleton_subset_iff.2 ⟨hOO' hx.1, (M.mem_boundary_iff x).2 hx.2⟩))
  rintro z ⟨⟨hzU, hzO⟩, hzb⟩
  have hFz : M.ϕ.obj z ∈ O' ∩ A.X.PObj.boundary := ⟨hOO' hzO, (M.mem_boundary_iff z).2 hzb⟩
  obtain ⟨hP, -⟩ := hs'.1 _ hFz
  have hFzU : A.P (s' (M.ϕ.obj z)) ∈ U₀' := by
    rw [hP]; exact hi.toLocalIso.base.mapsTo hzU
  have hw : C.P (hi.toLocalIso.Ψ (s' (M.ϕ.obj z))) = z := by
    rw [hi.toLocalIso.covers_inv _ hFzU, hP]
    exact hi.toLocalIso.base.left_inv z hzU
  refine (M.pullSec_eq_iff hP hw).2 ?_
  exact (hi.toLocalIso.zero.right_inv _ hFzU).symm

end PullMap

end SBLocalization

end Polyfold
