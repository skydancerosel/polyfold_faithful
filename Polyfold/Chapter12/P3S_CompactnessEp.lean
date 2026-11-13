import Polyfold.Chapter8.Book2021
import Polyfold.Chapter5.Book2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III:
**Definition 12.1.1** and the remark after it (p. 569; 2017: Definition 12.1), **Definition 12.4.1**
(p. 587; 2017: Definition 12.11), **Theorem 12.4.2** (pp. 587–588; 2017: Theorem 12.6) and
**Lemma 12.4.4** (p. 589; 2017: Lemma 12.3).

# Sc-Fredholm section functors: regularity on morphisms and compactness

## The text, paraphrased

(Definition 12.1.1) An sc-smooth section functor `f` of a strong bundle `(P : W → X, μ)` over an
ep-groupoid is sc-Fredholm if it is an sc-Fredholm section of `W → X` over the object
M-polyfold.  (After it) `f` is regularizing on objects, and also on morphisms: if `φ ∈ 𝐗_m` and
`f(φ) ∈ 𝐖_{m,m+1}`, then `f(s φ) = s(f(φ))` gives `s(φ) ∈ X_{m+1}`, so `φ ∈ 𝐗_{m+1}`; the germs at
smooth objects have filled versions conjugated to basic germs.
(Definition 12.4.1) With `S_f = {x | f(x) = 0}`: (1) compact solution set: `|S_f|` compact;
(2) proper: `|S_f|` compact and for every auxiliary norm `N` a saturated open `U ⊇ S_f` such that
the orbit space of `{x ∈ U | N(f(x)) ≤ 1}` has compact closure in `|X|`; (3) proper`<∞`: the same
for `N(f(x)) ≤ C`, every `0 < C < ∞`, with one `U`.  (Theorem 12.4.2) For sc-Fredholm `f` over
`X` with `|X|` paracompact the three are equivalent.  *Proof*: local compactness at a
representative of each point of `|S_f|` (Theorem 5.2.2), a finite subcover, and the union of the
saturations.  (Lemma 12.4.4) (1) `cl_{|X|}(|Σ|) = |cl_X(Σ)|` for saturated `Σ`; (2) the same for
`Σ` with compact closure.

## What is formalized

* **Definition 12.1.1**: `EpStrongBundle.definition_12_1_1` (it is Definition 8.3.4 (3),
  `IsScFredholmSectionFunctor`, unfolded).  The remark: `remark_12_1_1_regularizing_obj`,
  `remark_12_1_1_regularizing_mor` (morphisms, with `f(φ) = (φ, f(s φ)) ∈ 𝐗 ₛ×_P W`),
  `remark_12_1_1_germ`.
* **Lemma 12.4.4**: `EpGroupoid.lemma_12_4_4_1`, `lemma_12_4_4_2`, and the consequence
  `EpGroupoid.isClosed_image_π_of_isSaturated` (`π` maps saturated closed sets to closed sets).
* **Definition 12.4.1**: `EpStrongBundle.HasCompactSolutionSetEp`, `IsProperFunctor`,
  `IsProperLtInftyFunctor`.
* The local step: `exists_nhds_isCompact_closure_auxLe` (Part I, the local step of the proof of
  Theorem 5.2.2 at a zero), and the invariance `EpStrongBundle.auxLe_tgt_of_auxLe_src`
  (`N(f(t φ)) = N(f(s φ))` for a section functor and an auxiliary norm of Definition 8.3.5).
* **Theorem 12.4.2**: `EpStrongBundle.theorem_12_4_2` (the three statements as a `TFAE`), with the
  parts `IsProperLtInftyFunctor.isProperFunctor`, `IsProperFunctor.hasCompactSolutionSetEp` and
  `isProperLtInftyFunctor_of_hasCompactSolutionSetEp`.

## Reading

* **Paracompactness of `|X|`** is a hypothesis of Theorem 12.4.2, kept and not used: it only
  guarantees that auxiliary norms exist, while (1)–(3) quantify over all of them.
* **The proof's labels** "(3) ⇒ (2)", "(2) ⇒ (1)", "(1) ⇒ (3)" are presumably (3) ⇒ (1),
  (1) ⇒ (2), (2) ⇒ (3), which is what their arguments show; the cycle is closed either way.
* **The proof's shrinking** to neighbourhoods with the natural action and `cl_{|X|}|U| = |cl_X U|`
  is not needed: the closure of `|{x ∈ U | N(f(x)) ≤ C}|` lies in the finite union of the compact
  sets `π(cl_X Σ_i^C)` (`π` continuous, `|X|` Hausdorff, Lemma 7.3.4).
* "`N(f(x)) ≤ C`" is Part I's `AuxLe N (f x) C` (`N = +∞` off `W_{0,1}`, as the text extends `N`).
  The orbit space of a set `A ⊆ X` is `π(A) ⊆ |X|`.
* **Morphism regularity.**  `f(φ) ∈ 𝐖_{m,m+1}` is read in the pull-back strong bundle
  `𝐗 ₛ×_P W → 𝐗`; the pull-back projection is a strong bundle map, so `f(s φ) ∈ W_{m,m+1}`.
-/

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u v

/-! ### Lemma 12.4.4 -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **Lemma 12.4.4 (1), p. 589** (2017: Lemma 12.3 (1)): for a saturated `A ⊆ X`,
`cl_{|X|}(|A|) = |cl_X(A)|`.  (`π` is open, so `π⁻¹(cl B) = cl(π⁻¹ B)`.) -/
theorem lemma_12_4_4_1 {A : Set Obj} (hA : X.IsSaturated A) :
    closure (X.π '' A) = X.π '' closure A := by
  have h := (X.proposition_7_1_8).preimage_closure_eq_closure_preimage X.continuous_π (X.π '' A)
  have hA' : X.π ⁻¹' (X.π '' A) = A := hA
  rw [hA'] at h
  rw [← h, image_preimage_eq _ X.surjective_π]

/-- **Lemma 12.4.4 (2), p. 589** (2017: Lemma 12.3 (2)): for `A ⊆ X` with compact closure,
`cl_{|X|}(|A|) = |cl_X(A)|`. -/
theorem lemma_12_4_4_2 {A : Set Obj} (hA : IsCompact (closure A)) :
    closure (X.π '' A) = X.π '' closure A := by
  have hK : IsCompact (X.π '' closure A) := hA.image X.continuous_π
  refine Subset.antisymm (closure_minimal (image_mono subset_closure) hK.isClosed) ?_
  exact image_closure_subset_closure_image X.continuous_π

/-- `π` maps saturated closed sets to closed sets (Lemma 12.4.4 (1)). -/
theorem isClosed_image_π_of_isSaturated {A : Set Obj} (hA : X.IsSaturated A)
    (hAc : IsClosed A) : IsClosed (X.π '' A) := by
  rw [← closure_eq_iff_isClosed, X.lemma_12_4_4_1 hA, hAc.closure_eq]

end EpGroupoid

/-! ### The local step of Theorem 5.2.2 at a zero -/

section LocalStep

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]

open StrongBundle

variable {P : Y → Z} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PZ P} {f : Z → Y}

/-- **The local step of Theorem 5.2.2** (2021, p. 210; used in the proof of Theorem 12.4.2): for an
sc-Fredholm section `f`, an auxiliary norm `N` and a zero `x` of `f`, there is an open `V ∋ x`
such that `cl{y ∈ V | N(f(y)) ≤ C}` is compact for every `C > 0` (the step `hloc` of
`theorem_5_2_2`). -/
theorem exists_nhds_isCompact_closure_auxLe (hf : B.IsScFredholmSection f) {N : B.One → ℝ}
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

/-! ### Definitions 12.1.1, 12.4.1 and Theorem 12.4.2 -/

section Functors

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable (E : EpStrongBundle X B)

/-! #### Definition 12.1.1 and the remark after it -/

/-- **Definition 12.1.1, p. 569** (2017: Definition 12.1): an sc-smooth section functor `f` is an
**sc-Fredholm section functor** if it is an sc-Fredholm section of `W → X` over the object
M-polyfold.  This is Definition 8.3.4 (3) of the project (`IsScFredholmSectionFunctor`). -/
theorem definition_12_1_1 (f : Obj → W) :
    E.IsScFredholmSectionFunctor f ↔ E.IsScSmoothSectionFunctor f ∧ B.IsScFredholmSection f :=
  Iff.rfl

variable {E}

/-- **The remark after Definition 12.1.1, p. 569**, objects: `f` is regularizing, `x ∈ X_m` and
`f(x) ∈ W_{m,m+1}` give `x ∈ X_{m+1}`. -/
theorem remark_12_1_1_regularizing_obj {f : Obj → W} (hf : E.IsScFredholmSectionFunctor f)
    {m : ℕ} {x : Obj} (hx : x ∈ X.PObj.levelSet m) (hfx : f x ∈ B.doubleLevel m (m + 1)) :
    x ∈ X.PObj.levelSet (m + 1) :=
  hf.2.regularizing m x hx hfx

/-- **The remark after Definition 12.1.1, p. 569**, morphisms: for a morphism `φ ∈ 𝐗_m` with
`f(φ) = (φ, f(s φ)) ∈ 𝐖_{m,m+1}` (the double filtration of the pull-back bundle
`𝐗 ₛ×_P W → 𝐗`), `φ ∈ 𝐗_{m+1}`. -/
theorem remark_12_1_1_regularizing_mor {f : Obj → W} (hf : E.IsScFredholmSectionFunctor f)
    {m : ℕ} {φ : Mor} (hφ : φ ∈ X.PMor.levelSet m)
    (hfφ : haveI := B.paracompactSpace_pullback X.PMor X.src
      sectionPair hf.2.isScSmooth.1 φ ∈ (B.pullback X.isScSmoothMap_src).doubleLevel m (m + 1)) :
    φ ∈ X.PMor.levelSet (m + 1) := by
  have := B.paracompactSpace_pullback X.PMor X.src
  have hw : f (X.src φ) ∈ B.doubleLevel m (m + 1) :=
    (B.isStrongBundleMap_pullbackProj' X.isScSmoothMap_src).mapsTo_doubleLevel
      (Nat.le_refl _) hfφ
  have hs : X.src φ ∈ X.PObj.levelSet m := (X.mem_levelSet_src_iff φ m).2 hφ
  exact (X.mem_levelSet_src_iff φ (m + 1)).1 (hf.2.regularizing m _ hs hw)

/-- **The remark after Definition 12.1.1, p. 569**, germs: at every smooth object the germ of `f`
is an sc-Fredholm germ (a filled version conjugated, after subtracting an sc⁺-germ, to a basic
germ: Part I's Definition 3.1.11 in the germ reading, `IsScFredholmGerm`). -/
theorem remark_12_1_1_germ {f : Obj → W} (hf : E.IsScFredholmSectionFunctor f) {x : Obj}
    (hx : x ∈ X.PObj.smoothSet) : B.IsScFredholmGerm f x :=
  hf.2.germ x hx

/-! #### Invariance of `N ∘ f` -/

/-- For a section functor `f` and an auxiliary norm `N` of Definition 8.3.5,
`N(f(s φ)) ≤ C` implies `N(f(t φ)) ≤ C` (`f(t φ) = μ(φ, f(s φ))` and `N ∘ μ(φ, ·) = N`). -/
theorem auxLe_tgt_of_auxLe_src {f : Obj → W} (hfs : IsSection P f)
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

/-! #### Definition 12.4.1 -/

variable (E)

/-- **Definition 12.4.1 (1), p. 587** (2017: Definition 12.11 (1)): `f` has a **compact solution
set** (in the ep-groupoid sense): the orbit space `|S_f| = π(S_f)` of `S_f = {x | f(x) = 0}` is
compact. -/
def HasCompactSolutionSetEp (_E : EpStrongBundle X B) (f : Obj → W) : Prop :=
  IsCompact (X.π '' solutionSet P f)

/-- **Definition 12.4.1 (2), p. 587** (2017: Definition 12.11 (2)): `f` is **proper**: `|S_f|` is
compact and for every auxiliary norm `N` (Definition 8.3.5) there is a saturated open `U ⊇ S_f`
such that the orbit space of `{x ∈ U | N(f(x)) ≤ 1}` has compact closure in `|X|`. -/
def IsProperFunctor (f : Obj → W) : Prop :=
  IsCompact (X.π '' solutionSet P f) ∧ ∀ N : B.One → ℝ, E.IsAuxNorm N →
    ∃ U : Set Obj, IsOpen U ∧ X.IsSaturated U ∧ solutionSet P f ⊆ U ∧
      IsCompact (closure (X.π '' {x ∈ U | B.AuxLe N (f x) 1}))

/-- **Definition 12.4.1 (3), p. 587** (2017: Definition 12.11 (3)): `f` is **proper`<∞`**:
`|S_f|` is compact and for every auxiliary norm `N` there is a saturated open `U ⊇ S_f` such
that for every `0 < C < ∞` the orbit space of `{x ∈ U | N(f(x)) ≤ C}` has compact closure
in `|X|`. -/
def IsProperLtInftyFunctor (f : Obj → W) : Prop :=
  IsCompact (X.π '' solutionSet P f) ∧ ∀ N : B.One → ℝ, E.IsAuxNorm N →
    ∃ U : Set Obj, IsOpen U ∧ X.IsSaturated U ∧ solutionSet P f ⊆ U ∧
      ∀ C : ℝ, 0 < C → IsCompact (closure (X.π '' {x ∈ U | B.AuxLe N (f x) C}))

variable {E}

/-- (3) ⇒ (1) of Theorem 12.4.2 (the text's "(3) ⇒ (2)"): take `C = 1`. -/
theorem IsProperLtInftyFunctor.isProperFunctor {f : Obj → W} (h : E.IsProperLtInftyFunctor f) :
    E.IsProperFunctor f := by
  refine ⟨h.1, fun N hN => ?_⟩
  obtain ⟨U, hUo, hUs, hSU, hC⟩ := h.2 N hN
  exact ⟨U, hUo, hUs, hSU, hC 1 one_pos⟩

/-- (1) ⇒ (2) of Theorem 12.4.2 (the text's "(2) ⇒ (1)"). -/
theorem IsProperFunctor.hasCompactSolutionSetEp {f : Obj → W} (h : E.IsProperFunctor f) :
    E.HasCompactSolutionSetEp f :=
  h.1

/-- (2) ⇒ (3) of Theorem 12.4.2 (the text's "(1) ⇒ (3)"): an sc-Fredholm section functor with
compact solution set is proper`<∞`.  Near a representative `x` of each point of `|S_f|` the local
step of Theorem 5.2.2 gives `V(x)`; finitely many `|V(x_i)|` cover `|S_f|`; `U = π⁻¹(⋃ |V(x_i)|)`;
and `|{x ∈ U | N(f(x)) ≤ C}| ⊆ ⋃ π(cl{y ∈ V(x_i) | N(f(y)) ≤ C})` by the invariance of `N ∘ f`. -/
theorem isProperLtInftyFunctor_of_hasCompactSolutionSetEp {f : Obj → W}
    (hf : E.IsScFredholmSectionFunctor f) (hS : E.HasCompactSolutionSetEp f) :
    E.IsProperLtInftyFunctor f := by
  classical
  refine ⟨hS, fun N hN => ?_⟩
  obtain ⟨hsm, hfun⟩ : E.IsScSmoothSectionFunctor f := hf.1
  have hloc := fun x (hx : x ∈ solutionSet P f) =>
    exists_nhds_isCompact_closure_auxLe hf.2 hN.isAuxNorm hx
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
      have := auxLe_tgt_of_auxLe_src hsm.1 hfun hN φ (by rw [hφs]; exact hyN)
      rwa [hφt] at this
    exact mem_iUnion₂.2 ⟨x, hx, ⟨y', subset_closure ⟨hy'V, hN'⟩, hy'y⟩⟩

/-- **Theorem 12.4.2, pp. 587–588** (2017: Theorem 12.6): for an sc-Fredholm section functor `f` of
a strong bundle over an ep-groupoid with paracompact orbit space, the following are equivalent:
(1) `f` is proper, (2) `f` has a compact solution set, (3) `f` is proper`<∞`
(Definition 12.4.1).  The paracompactness of `|X|` is kept as in the text and not used. -/
theorem theorem_12_4_2 {f : Obj → W} (hf : E.IsScFredholmSectionFunctor f)
    (_hpara : X.HasParacompactOrbitSpace) :
    List.TFAE [E.IsProperFunctor f, E.HasCompactSolutionSetEp f, E.IsProperLtInftyFunctor f] := by
  tfae_have 3 → 1 := IsProperLtInftyFunctor.isProperFunctor
  tfae_have 1 → 2 := IsProperFunctor.hasCompactSolutionSetEp
  tfae_have 2 → 3 := isProperLtInftyFunctor_of_hasCompactSolutionSetEp hf
  tfae_finish

end EpStrongBundle

end Functors

end Polyfold
