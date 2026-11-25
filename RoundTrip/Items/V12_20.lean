import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V12_20

/-! Round trip for V12_20 (2021 Theorem 12.4.2, pp. 587–588: proper, compact solution set and
proper`<∞` agree for sc-Fredholm section functors).

The item lists `theorem_12_4_2` (a `List.TFAE` of the three notions of Definition 12.4.1, for an
sc-Fredholm section functor over an ep-groupoid with paracompact `|X|`) and the parts of its
proof: `isProperLtInftyFunctor_of_hasCompactSolutionSetEp`, `IsProperFunctor.hasCompactSolutionSetEp`,
`IsProperLtInftyFunctor.isProperFunctor`, `auxLe_tgt_of_auxLe_src` and the Part I local step
`exists_nhds_isCompact_closure_auxLe`.  `A` is the conjunction of their types, universes
`.{0, 0}` (objects and total space in `Type`).

* `A_to_B`: `theorem_12_4_2` read off as the two equivalences of `B`
  (`f ∈ E.fredholmSectionFunctors` is `E.IsScFredholmSectionFunctor f` by definition).
* `B_to_A`: `theorem_12_4_2` from `B` (pullback instance from
  `StrongBundle.paracompactSpace_pullback`).  The proof's parts do not follow from `B`: they carry
  no paracompactness of `|X|`, and the Part I step is about one M-polyfold.  They are re-proved
  outright by copying the project's proofs (non-item lemmas: `exists_nbhd_isCompact_closure_bdd`,
  `IsAuxNorm.exists_norm_liftOne_le`, `exists_oneVal_eq_μ`, `proposition_7_1_8`, ...).
-/

namespace RoundTrip.V12_20
open Polyfold
open Set Function Filter Topology

universe u v

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.theorem_12_4_2.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isProperLtInftyFunctor_of_hasCompactSolutionSetEp.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsProperFunctor.hasCompactSolutionSetEp.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsProperLtInftyFunctor.isProperFunctor.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.auxLe_tgt_of_auxLe_src.{0, 0}) ∧
  (type_of% @Polyfold.exists_nhds_isCompact_closure_auxLe.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.theorem_12_4_2.{0, 0}, @Polyfold.EpStrongBundle.isProperLtInftyFunctor_of_hasCompactSolutionSetEp.{0, 0}, @Polyfold.EpStrongBundle.IsProperFunctor.hasCompactSolutionSetEp.{0, 0}, @Polyfold.EpStrongBundle.IsProperLtInftyFunctor.isProperFunctor.{0, 0}, @Polyfold.EpStrongBundle.auxLe_tgt_of_auxLe_src.{0, 0}, @Polyfold.exists_nhds_isCompact_closure_auxLe.{0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h, -⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E hX f hf
  have t := h (E := E) hf hX
  exact ⟨t.out 0 1, t.out 1 2⟩

/-! ### The proof's parts, re-proved outright (the project's proofs, copied) -/

section LocalStep

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]

open StrongBundle

variable {P : Y → Z} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PZ P} {f : Z → Y}

theorem exists_nhds_isCompact_closure_auxLe' (hf : B.IsScFredholmSection f) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) {x : Z} (hx : x ∈ solutionSet P f) :
    ∃ V : Set Z, IsOpen V ∧ x ∈ V ∧
      ∀ C : ℝ, 0 < C → IsCompact (closure {y ∈ V | B.AuxLe N (f y) C}) := by
  have hsec := hf.isScSmooth.1
  obtain ⟨c, hc, hxc, V, hVo, hxV, hVc, hK⟩ :=
    exists_nbhd_isCompact_closure_bdd (hf.germ x (hf.mem_smoothSet_of_isZeroAt hx))
  obtain ⟨V₁, hV₁o, hxV₁, -, A, hA, hV₁⟩ := hN.exists_norm_liftOne_le hc hxc
  refine ⟨V ∩ V₁, hVo.inter hV₁o, ⟨hxV, hxV₁⟩, fun C _ =>
    (hK (A * C)).of_isClosed_subset isClosed_closure (closure_mono ?_)⟩
  rintro y ⟨⟨hyV, hyV₁⟩, hy1, hyN⟩
  refine ⟨hyV, (c.liftOne (f y)).2, ?_, ?_⟩
  · exact toBase_liftOne_snd hc (c.mem_source_of_proj (by rw [hsec y]; exact hVc hyV)) hy1
  · have := hV₁ (B.oneMk (f y) hy1) (by rw [oneVal_oneMk, hsec y]; exact hyV₁)
    rw [oneVal_oneMk] at this
    calc ‖(c.liftOne (f y)).2‖ ≤ A * N (B.oneMk (f y) hy1) := this
      _ ≤ A * C := mul_le_mul_of_nonneg_left hyN hA.le

end LocalStep

section Functors
open EpStrongBundle

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

variable {E : EpStrongBundle X B}

theorem auxLe_tgt_of_auxLe_src' {f : Obj → W} (hfs : IsSection P f)
    (hfun : E.IsFunctorialSection hfs) {N : B.One → ℝ} (hN : E.IsAuxNorm N) (φ : Mor) {C : ℝ}
    (h : B.AuxLe N (f (X.src φ)) C) : B.AuxLe N (f (X.tgt φ)) C := by
  obtain ⟨hy1, hle⟩ := h
  obtain ⟨k, hk⟩ := exists_oneVal_eq_μ E (B.oneMk _ hy1) φ (hfs (X.src φ))
  have hft : f (X.tgt φ) = B.oneVal k := by rw [hfun φ, hk]; rfl
  have hmem : f (X.tgt φ) ∈ B.oneSet := hft ▸ B.oneVal_mem k
  refine ⟨hmem, ?_⟩
  have e : B.oneMk (f (X.tgt φ)) hmem = k := B.oneVal_injective hft
  rw [e, hN.map_μ k (B.oneMk _ hy1) φ (hfs (X.src φ)) hk]
  exact hle

theorem isProperFunctor' {f : Obj → W} (h : E.IsProperLtInftyFunctor f) :
    E.IsProperFunctor f := by
  refine ⟨h.1, fun N hN => ?_⟩
  obtain ⟨U, hUo, hUs, hSU, hC⟩ := h.2 N hN
  exact ⟨U, hUo, hUs, hSU, hC 1 one_pos⟩

theorem hasCompactSolutionSetEp' {f : Obj → W} (h : E.IsProperFunctor f) :
    E.HasCompactSolutionSetEp f :=
  h.1

theorem isProperLtInftyFunctor_of_hasCompactSolutionSetEp' {f : Obj → W}
    (hf : E.IsScFredholmSectionFunctor f) (hS : E.HasCompactSolutionSetEp f) :
    E.IsProperLtInftyFunctor f := by
  classical
  refine ⟨hS, fun N hN => ?_⟩
  obtain ⟨hsm, hfun⟩ : E.IsScSmoothSectionFunctor f := hf.1
  have hloc := fun x (hx : x ∈ solutionSet P f) =>
    exists_nhds_isCompact_closure_auxLe' hf.2 hN.isAuxNorm hx
  choose! V hVo hxV hVK using hloc
  obtain ⟨t, htS, htfin, hcover⟩ := IsCompact.elim_finite_subcover_image (b := solutionSet P f)
    (c := fun x => X.π '' V x) hS (fun x hx => X.proposition_7_1_8 _ (hVo x hx))
    (by rintro _ ⟨x, hx, rfl⟩; exact mem_biUnion hx ⟨x, hxV x hx, rfl⟩)
  set O : Set X.OrbitSpace := ⋃ x ∈ t, X.π '' V x with hO
  have hOo : IsOpen O := isOpen_biUnion fun x hx => X.proposition_7_1_8 _ (hVo x (htS hx))
  refine ⟨X.π ⁻¹' O, hOo.preimage X.continuous_π, ?_, fun y hy => hcover ⟨y, hy, rfl⟩,
    fun C hC => ?_⟩
  · change X.π ⁻¹' (X.π '' (X.π ⁻¹' O)) = X.π ⁻¹' O
    rw [image_preimage_eq _ X.surjective_π]
  · set K : Set X.OrbitSpace := ⋃ x ∈ t, X.π '' closure {y ∈ V x | B.AuxLe N (f y) C} with hK
    have hKc : IsCompact K := htfin.isCompact_biUnion fun x hx =>
      (hVK x (htS hx) C hC).image X.continuous_π
    refine hKc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hKc.isClosed)
    rintro _ ⟨y, ⟨hyU, hyN⟩, rfl⟩
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (show X.π y ∈ O from hyU)
    obtain ⟨y', hy'V, hy'y⟩ := hyx
    obtain ⟨φ, hφs, hφt⟩ := X.π_eq_π_iff.1 hy'y.symm
    have hN' : B.AuxLe N (f y') C := by
      have := auxLe_tgt_of_auxLe_src' hsm.1 hfun hN φ (by rw [hφs]; exact hyN)
      rwa [hφt] at this
    exact mem_iUnion₂.2 ⟨x, hx, ⟨y', subset_closure ⟨hy'V, hN'⟩, hy'y⟩⟩

end Functors

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, @isProperLtInftyFunctor_of_hasCompactSolutionSetEp'.{0, 0},
    @hasCompactSolutionSetEp'.{0, 0}, @isProperFunctor'.{0, 0}, @auxLe_tgt_of_auxLe_src'.{0, 0},
    @exists_nhds_isCompact_closure_auxLe'.{0, 0}⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E f hf hX
  have := B.paracompactSpace_pullback X.PMor X.src
  obtain ⟨h12, h23⟩ := hB Obj Mor X W P B E hX f hf
  tfae_have 1 ↔ 2 := h12
  tfae_have 2 ↔ 3 := h23
  tfae_finish

#rt_check RoundTrip.V12_20.A_to_B [Polyfold.EpStrongBundle.theorem_12_4_2,
  Polyfold.EpStrongBundle.isProperLtInftyFunctor_of_hasCompactSolutionSetEp,
  Polyfold.EpStrongBundle.IsProperFunctor.hasCompactSolutionSetEp,
  Polyfold.EpStrongBundle.IsProperLtInftyFunctor.isProperFunctor,
  Polyfold.EpStrongBundle.auxLe_tgt_of_auxLe_src,
  Polyfold.exists_nhds_isCompact_closure_auxLe]
#rt_check RoundTrip.V12_20.B_to_A [Polyfold.EpStrongBundle.theorem_12_4_2,
  Polyfold.EpStrongBundle.isProperLtInftyFunctor_of_hasCompactSolutionSetEp,
  Polyfold.EpStrongBundle.IsProperFunctor.hasCompactSolutionSetEp,
  Polyfold.EpStrongBundle.IsProperLtInftyFunctor.isProperFunctor,
  Polyfold.EpStrongBundle.auxLe_tgt_of_auxLe_src,
  Polyfold.exists_nhds_isCompact_closure_auxLe]
#rt_overlap RoundTrip.V12_20.B_to_A [Polyfold.EpStrongBundle.theorem_12_4_2,
  Polyfold.EpStrongBundle.isProperLtInftyFunctor_of_hasCompactSolutionSetEp,
  Polyfold.EpStrongBundle.IsProperFunctor.hasCompactSolutionSetEp,
  Polyfold.EpStrongBundle.IsProperLtInftyFunctor.isProperFunctor,
  Polyfold.EpStrongBundle.auxLe_tgt_of_auxLe_src,
  Polyfold.exists_nhds_isCompact_closure_auxLe]

end RoundTrip.V12_20
