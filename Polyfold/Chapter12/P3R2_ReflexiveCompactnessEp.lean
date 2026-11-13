import Polyfold.Chapter12.P3R2_ReflexiveAuxNormEp
import Polyfold.Chapter12.P3S_CompactnessEp
import Polyfold.Chapter5.P3R_ReflexiveCompactness2021
import Polyfold.Chapter12.P3N_GoodNeighborhood
import Polyfold.Chapter12.P3N_AuxNormExtension

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 12,
§12.4, pp. 588–592: **Definition 12.4.3, Proposition 12.4.5, Theorem 12.4.6** (2017:
Definition 12.12, Proposition 12.7, Theorem 12.7).

# Reflexive local compactness for sc-Fredholm section functors

## The text, paraphrased

(Definition 12.4.3) For a strong bundle over an ep-groupoid with reflexive `(0, 1)`-fibres and an
sc-smooth, regularizing section functor `f`: `f` has the ep-groupoid reflexive local compactness
property if for every reflexive auxiliary norm `N` (a functor) and every object `x` there is an
open `U(x) ∋ x` with `cl_X {y ∈ U(x) | N(f(y)) ≤ 1}` compact.  (Proposition 12.4.5) Equivalent:
(1) this property; (2) for every reflexive `N` and `z ∈ |X|` a saturated open `Ũ` with `z ∈ |Ũ|`
and `|cl_X {y ∈ Ũ | N(f(y)) ≤ 1}|` compact; (3) the same with `cl_{|X|}(|{y ∈ Ũ | N(f(y)) ≤ 1}|)`
compact.  (Theorem 12.4.6) `X` tame, `|X|` paracompact, reflexive fibres, `N` reflexive, `f`
sc-Fredholm with compact solution set and the reflexive local compactness property, and `U_∂` an
open saturated neighbourhood in `∂X` of `S_∂ = S_f ∩ ∂X` with `cl_{|X|}(|{y ∈ U_∂ | N(f(y)) ≤ 1}|)`
compact.  Then there is a saturated open `U ⊇ S_f` with `U ∩ ∂X = U_∂` and
`cl_{|X|}(|{x ∈ U | N(f(x)) ≤ 1}|)` compact.

## What is formalized

* **Definition 12.4.3**: `EpStrongBundle.HasReflexiveLocalCompactnessEp` (it follows from Part I's
  Definition 5.2.6 on the object bundle: `hasReflexiveLocalCompactnessEp_of_strong`).
* **Proposition 12.4.5**: `proposition_12_4_5` (book hypotheses) and
  `proposition_12_4_5_of_functorial` (every section functor; the reflexive fibres, sc-smoothness
  and the regularizing property are not used).  The direction (3) ⇒ (1) uses the properness of
  `t : s⁻¹(cl V₀) → X` (`isCompact_closure_of_isProperMap`: a set inside `V₀` whose orbit set has
  compact closure has compact closure in `X`), with the lift of convergent sequences of `|X|`
  (`EpGroupoid.exists_lift_tendsto`).
* **Theorem 12.4.6**: `theorem_12_4_6` (book hypotheses) and `theorem_12_4_6_of_continuous` (for
  every continuous section functor with `|S_f|` compact and local compactness at the given `N`; no
  tameness, no paracompactness, no Fredholm property).  The proof is the text's, carried out in
  `|X|`: finitely many `|U(x̄ᵢ)|` cover `cl|{U_∂ ∩ {N∘f ≤ 1}}|`, the set `{N∘f > 1}` is open and
  saturated (Proposition 5.2.7 (2) and functoriality), finitely many interior neighbourhoods cover
  the rest of `|S_f|`, and `U` is the preimage of the union, cut down so that `U ∩ ∂X = U_∂`.

## Readings

* "`U_∂` open in `∂X`" is read as `U_∂ = W' ∩ ∂X` with `W'` open in `X`.
* In Proposition 12.4.5 (2), (3) the sets `Ũ` are saturated and open, as printed.
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

/-! ### Lifting convergent sequences of `|X|`, and compactness from properness -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **Convergent sequences of `|X|` lift**: if `|u_k| → |q|`, there are `v_k` with `|v_k| = |u_k|`
and `v_k → q` (`π` is open and `X` is first countable). -/
theorem exists_lift_tendsto {u : ℕ → Obj} {q : Obj}
    (h : Tendsto (fun k => X.π (u k)) atTop (𝓝 (X.π q))) :
    ∃ v : ℕ → Obj, (∀ k, X.π (v k) = X.π (u k)) ∧ Tendsto v atTop (𝓝 q) := by
  classical
  have := X.PObj.metrizableSpace
  obtain ⟨V, hV⟩ := (𝓝 q).exists_antitone_basis
  have hK : ∀ n, ∀ᶠ k in atTop, X.π (u k) ∈ X.π '' V n := fun n =>
    h (X.proposition_7_1_8.image_mem_nhds (hV.mem n))
  choose K hK using fun n => eventually_atTop.1 (hK n)
  set m : ℕ → ℕ := fun k => Nat.findGreatest (fun n => K n ≤ k) k with hm
  have hex : ∀ k, ∃ v, X.π v = X.π (u k) ∧ (K 0 ≤ k → v ∈ V (m k)) := by
    intro k
    by_cases hk : K 0 ≤ k
    · have hmk : K (m k) ≤ k := Nat.findGreatest_spec (P := fun n => K n ≤ k) (Nat.zero_le k) hk
      obtain ⟨v, hv, hvu⟩ := hK (m k) k hmk
      exact ⟨v, hvu, fun _ => hv⟩
    · exact ⟨u k, rfl, fun h => absurd h hk⟩
  choose v hvπ hvV using hex
  refine ⟨v, hvπ, hV.toHasBasis.tendsto_right_iff.2 fun n _ => ?_⟩
  filter_upwards [eventually_ge_atTop (max n (max (K n) (K 0)))] with k hk
  have hkn : n ≤ k := (le_max_left _ _).trans hk
  have hKn : K n ≤ k := ((le_max_left _ _).trans (le_max_right _ _)).trans hk
  have hK0 : K 0 ≤ k := ((le_max_right _ _).trans (le_max_right _ _)).trans hk
  have hnm : n ≤ m k := Nat.le_findGreatest hkn hKn
  exact hV.antitone hnm (hvV k hK0)

/-- **Compactness in `X` from compactness in `|X|`, inside a proper neighbourhood**: if
`t : s⁻¹(cl V₀) → X` is proper, `S ⊆ V₀` and `cl_{|X|}(|S|)` is compact, then `cl_X(S)` is
compact.  (A sequence in `cl S` has a subsequence whose orbits converge; lift the limit, take
connecting morphisms and use the properness.) -/
theorem isCompact_closure_of_isProperMap {V₀ S : Set Obj}
    (hprop : IsProperMap ((X.src ⁻¹' closure V₀).domRestrict X.tgt)) (hSV : S ⊆ V₀)
    (hC : IsCompact (closure (X.π '' S))) : IsCompact (closure S) := by
  have := X.PObj.metrizableSpace
  refine IsSeqCompact.isCompact fun y hy => ?_
  have hyC : ∀ k, X.π (y k) ∈ closure (X.π '' S) := fun k =>
    image_closure_subset_closure_image X.continuous_π ⟨y k, hy k, rfl⟩
  obtain ⟨c, -, σ, hσ, hc⟩ := hC.isSeqCompact hyC
  obtain ⟨q, rfl⟩ := X.surjective_π c
  obtain ⟨v, hvπ, hv⟩ := X.exists_lift_tendsto (u := y ∘ σ) hc
  have hmor : ∀ k, ∃ φ, X.src φ = y (σ k) ∧ X.tgt φ = v k := fun k =>
    X.π_eq_π_iff.1 (hvπ k).symm
  choose φ hφs hφt using hmor
  obtain ⟨ψ, τ, hτ, hψ, -, -⟩ := X.exists_subseq_of_isProperMap hprop isClosed_closure
    Subset.rfl φ q (fun k => by rw [hφs k]; exact closure_mono hSV (hy (σ k)))
    (hv.congr fun k => (hφt k).symm)
  have h1 : Tendsto (fun k => X.src (φ (τ k))) atTop (𝓝 (X.src ψ)) :=
    (X.continuous_src.tendsto ψ).comp hψ
  have h2 : Tendsto (y ∘ (σ ∘ τ)) atTop (𝓝 (X.src ψ)) := h1.congr fun k => hφs (τ k)
  exact ⟨X.src ψ, isClosed_closure.mem_of_tendsto h2 (Eventually.of_forall fun k => hy _),
    σ ∘ τ, hσ.comp hτ, h2⟩

end EpGroupoid

section Compactness

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable (E : EpStrongBundle X B)

/-! ### Definition 12.4.3 -/

/-- **Definition 12.4.3, pp. 588–589** (2017: Definition 12.12): the section functor `f` has the
**ep-groupoid reflexive local compactness property**: for every reflexive auxiliary norm `N`
(Definition 12.2.10, a functor) and every object `x` there is an open `U(x) ∋ x` with
`cl_X {y ∈ U(x) | N(f(y)) ≤ 1}` compact.  (The standing assumptions, reflexive `(0, 1)`-fibres and
`f` sc-smooth and regularizing, are hypotheses of the statements using it.) -/
def HasReflexiveLocalCompactnessEp (f : Obj → W) : Prop :=
  ∀ N : B.One → ℝ, E.IsReflexiveAuxNorm N → ∀ x : Obj, ∃ U : Set Obj, IsOpen U ∧ x ∈ U ∧
    IsCompact (closure {y ∈ U | B.AuxLe N (f y) 1})

variable {E}

/-- Part I's reflexive local compactness (Definition 5.2.6) of the object bundle gives the
ep-groupoid one (every reflexive auxiliary norm of Definition 12.2.10 is one of Definition
5.1.7). -/
theorem hasReflexiveLocalCompactnessEp_of_strong {f : Obj → W}
    (h : B.HasReflexiveLocalCompactness f) : E.HasReflexiveLocalCompactnessEp f :=
  fun N hN => h N hN.toStrong

/-- For a section functor and an auxiliary norm, `{x | N(f(x)) ≤ C}` is saturated. -/
theorem isSaturated_setOf_auxLe {f : Obj → W} (hfs : IsSection P f)
    (hfun : E.IsFunctorialSection hfs) {N : B.One → ℝ} (hN : E.IsAuxNorm N) (C : ℝ) :
    X.IsSaturated {x | B.AuxLe N (f x) C} :=
  X.isSaturated_iff.2 fun φ h => auxLe_tgt_of_auxLe_src hfs hfun hN φ h

/-- The intersection of two saturated sets is saturated. -/
theorem _root_.Polyfold.EpGroupoid.isSaturated_inter {A A' : Set Obj} (hA : X.IsSaturated A)
    (hA' : X.IsSaturated A') : X.IsSaturated (A ∩ A') :=
  X.isSaturated_iff.2 fun φ h => ⟨X.isSaturated_iff.1 hA φ h.1, X.isSaturated_iff.1 hA' φ h.2⟩

/-! ### Proposition 12.4.5 -/

/-- **Proposition 12.4.5 for every section functor**: (1) the reflexive local compactness property,
(2) for every reflexive `N` and `z ∈ |X|` a saturated open `Ũ` with `z ∈ |Ũ|` and
`|cl_X {y ∈ Ũ | N(f(y)) ≤ 1}|` compact, (3) the same with `cl_{|X|}(|{y ∈ Ũ | N(f(y)) ≤ 1}|)`
compact, are equivalent. -/
theorem proposition_12_4_5_of_functorial {f : Obj → W} (hfs : IsSection P f)
    (hfun : E.IsFunctorialSection hfs) :
    List.TFAE [E.HasReflexiveLocalCompactnessEp f,
      ∀ N : B.One → ℝ, E.IsReflexiveAuxNorm N → ∀ z : X.OrbitSpace, ∃ U : Set Obj, IsOpen U ∧
        X.IsSaturated U ∧ z ∈ X.π '' U ∧
        IsCompact (X.π '' closure {y ∈ U | B.AuxLe N (f y) 1}),
      ∀ N : B.One → ℝ, E.IsReflexiveAuxNorm N → ∀ z : X.OrbitSpace, ∃ U : Set Obj, IsOpen U ∧
        X.IsSaturated U ∧ z ∈ X.π '' U ∧
        IsCompact (closure (X.π '' {y ∈ U | B.AuxLe N (f y) 1}))] := by
  have hsat : ∀ N : B.One → ℝ, E.IsAuxNorm N → ∀ U : Set Obj, X.IsSaturated U →
      X.IsSaturated {y ∈ U | B.AuxLe N (f y) 1} := fun N hN U hU =>
    EpGroupoid.isSaturated_inter hU (isSaturated_setOf_auxLe hfs hfun hN 1)
  tfae_have 2 ↔ 3 := by
    refine forall_congr' fun N => imp_congr_right fun hN => forall_congr' fun z =>
      exists_congr fun U => ?_
    constructor
    · rintro ⟨hUo, hUs, hz, hc⟩
      exact ⟨hUo, hUs, hz, by rw [X.lemma_12_4_4_1 (hsat N hN.toIsAuxNorm U hUs)]; exact hc⟩
    · rintro ⟨hUo, hUs, hz, hc⟩
      exact ⟨hUo, hUs, hz, by rw [← X.lemma_12_4_4_1 (hsat N hN.toIsAuxNorm U hUs)]; exact hc⟩
  tfae_have 1 → 3 := by
    intro h N hN z
    obtain ⟨x, rfl⟩ := X.surjective_π z
    obtain ⟨U, hUo, hxU, hUc⟩ := h N hN x
    refine ⟨X.satSet U, EpGroupoid.isOpen_satSet hUo, EpGroupoid.isSaturated_satSet U,
      ⟨x, EpGroupoid.subset_satSet U hxU, rfl⟩, ?_⟩
    have himg : X.π '' {y ∈ X.satSet U | B.AuxLe N (f y) 1} =
        X.π '' {y ∈ U | B.AuxLe N (f y) 1} := by
      refine Subset.antisymm ?_ (image_mono fun y hy => ⟨EpGroupoid.subset_satSet U hy.1, hy.2⟩)
      rintro _ ⟨y, ⟨⟨φ, hφs, hφt⟩, hyN⟩, rfl⟩
      refine ⟨X.tgt φ, ⟨hφt, ?_⟩, ?_⟩
      · exact auxLe_tgt_of_auxLe_src hfs hfun hN.toIsAuxNorm φ (by rw [hφs]; exact hyN)
      · rw [← hφs]; exact (X.π_src_eq_π_tgt φ).symm
    rw [himg, X.lemma_12_4_4_2 hUc]
    exact hUc.image X.continuous_π
  tfae_have 3 → 1 := by
    intro h N hN x
    obtain ⟨Ũ, hŨo, hŨs, hz, hc⟩ := h N hN (X.π x)
    have hxŨ : x ∈ Ũ := EpGroupoid.mem_of_π_mem_image hŨs hz
    obtain ⟨V₀, hV₀o, hxV₀, hprop⟩ := X.exists_isProperMap x
    refine ⟨Ũ ∩ V₀, hŨo.inter hV₀o, ⟨hxŨ, hxV₀⟩, ?_⟩
    refine X.isCompact_closure_of_isProperMap hprop (fun y hy => hy.1.2) ?_
    exact hc.of_isClosed_subset isClosed_closure
      (closure_mono (image_mono fun y hy => ⟨hy.1.1, hy.2⟩))
  tfae_finish

/-- **Proposition 12.4.5, p. 590** (2017: Proposition 12.7): for a strong bundle over an
ep-groupoid with reflexive `(0, 1)`-fibres and an sc-smooth, regularizing section functor `f`, the
following are equivalent: (1) `f` has the ep-groupoid reflexive local compactness property;
(2) for every reflexive auxiliary norm `N` and `z ∈ |X|` there is a saturated open `Ũ` with
`z ∈ |Ũ|` and `|cl_X {y ∈ Ũ | N(f(y)) ≤ 1}|` compact; (3) the same with
`cl_{|X|}(|{y ∈ Ũ | N(f(y)) ≤ 1}|)` compact.  The reflexive fibres and the regularizing property
are kept as in the text and not used (`proposition_12_4_5_of_functorial`). -/
theorem proposition_12_4_5 (_hB : E.HasReflexiveFibers) {f : Obj → W}
    (hf : E.IsScSmoothSectionFunctor f)
    (_hreg : ∀ m, ∀ x ∈ X.PObj.levelSet m, f x ∈ B.doubleLevel m (m + 1) →
      x ∈ X.PObj.levelSet (m + 1)) :
    List.TFAE [E.HasReflexiveLocalCompactnessEp f,
      ∀ N : B.One → ℝ, E.IsReflexiveAuxNorm N → ∀ z : X.OrbitSpace, ∃ U : Set Obj, IsOpen U ∧
        X.IsSaturated U ∧ z ∈ X.π '' U ∧
        IsCompact (X.π '' closure {y ∈ U | B.AuxLe N (f y) 1}),
      ∀ N : B.One → ℝ, E.IsReflexiveAuxNorm N → ∀ z : X.OrbitSpace, ∃ U : Set Obj, IsOpen U ∧
        X.IsSaturated U ∧ z ∈ X.π '' U ∧
        IsCompact (closure (X.π '' {y ∈ U | B.AuxLe N (f y) 1}))] := by
  obtain ⟨hsm, hfun⟩ := hf
  exact proposition_12_4_5_of_functorial hsm.1 hfun

/-! ### Theorem 12.4.6 -/

/-- **Theorem 12.4.6 for continuous section functors** (the text's proof uses only continuity of
`f`, compactness of `|S_f|`, the local compactness at the given `N`, the reflexive fibres and the
lower semicontinuity of `N`): if `U_∂ = W' ∩ ∂X` (`W'` open) is saturated, contains
`S_f ∩ ∂X`, and `cl_{|X|}(|{y ∈ U_∂ | N(f(y)) ≤ 1}|)` is compact, there is a saturated open
`U ⊇ S_f` with `U ∩ ∂X = U_∂` and `cl_{|X|}(|{x ∈ U | N(f(x)) ≤ 1}|)` compact. -/
theorem theorem_12_4_6_of_continuous (hB : E.HasReflexiveFibers) {N : B.One → ℝ}
    (hN : E.IsReflexiveAuxNorm N) {f : Obj → W} (hfs : IsSection P f) (hfc : Continuous f)
    (hfun : E.IsFunctorialSection hfs) (hS : IsCompact (X.π '' solutionSet P f))
    (hlc : ∀ x : Obj, ∃ U : Set Obj, IsOpen U ∧ x ∈ U ∧
      IsCompact (closure {y ∈ U | B.AuxLe N (f y) 1}))
    {Ub : Set Obj} (hUb : ∃ W' : Set Obj, IsOpen W' ∧ Ub = W' ∩ X.PObj.boundary)
    (hUbs : X.IsSaturated Ub) (hSUb : solutionSet P f ∩ X.PObj.boundary ⊆ Ub)
    (hcpt : IsCompact (closure (X.π '' {y ∈ Ub | B.AuxLe N (f y) 1}))) :
    ∃ U : Set Obj, IsOpen U ∧ X.IsSaturated U ∧ solutionSet P f ⊆ U ∧
      U ∩ X.PObj.boundary = Ub ∧ IsCompact (closure (X.π '' {x ∈ U | B.AuxLe N (f x) 1})) := by
  classical
  set A : Set Obj := {x | B.AuxLe N (f x) 1} with hAdef
  have hAc : IsClosed A := StrongBundle.isClosed_setOf_auxLe hB hfs hfc hN.toStrong
  have hAs : X.IsSaturated A := isSaturated_setOf_auxLe hfs hfun hN.toIsAuxNorm 1
  have hbs : X.IsSaturated X.PObj.boundary :=
    X.isSaturated_iff.2 fun φ h => (X.tgt_mem_boundary_iff φ).2 h
  have hbo : IsOpen X.PObj.boundaryᶜ := X.PObj.isClosed_boundary.isOpen_compl
  have hπo : ∀ V : Set Obj, IsOpen V → IsOpen (X.π '' V) := fun V hV => X.proposition_7_1_8 V hV
  choose Uq hUqo hxUq hUqc using hlc
  -- the boundary part: finitely many `|U(x̄ᵢ)|` cover `cl |{x ∈ U_∂ | N(f(x)) ≤ 1}|`
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover (fun q => X.π '' Uq q) (fun q => hπo _ (hUqo q))
    (fun z _ => by
      obtain ⟨q, rfl⟩ := X.surjective_π z
      exact mem_iUnion.2 ⟨q, q, hxUq q, rfl⟩)
  have hπA : IsClosed (X.π '' A) := X.isClosed_image_π_of_isSaturated hAs hAc
  set O1 : Set X.OrbitSpace := ⋃ q ∈ t, X.π '' Uq q with hO1
  set Ot : Set X.OrbitSpace := O1 ∪ (X.π '' A)ᶜ with hOt
  have hOto : IsOpen Ot := (isOpen_biUnion fun q _ => hπo _ (hUqo q)).union hπA.isOpen_compl
  have hUbOt : ∀ x ∈ Ub, X.π x ∈ Ot := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inl (ht (subset_closure ⟨x, ⟨hx, hxA⟩, rfl⟩))
    · exact Or.inr fun h => hxA (EpGroupoid.mem_of_π_mem_image hAs h)
  -- the interior solutions off `|Ũ|`
  have hS'c : IsCompact (X.π '' solutionSet P f \ Ot) := hS.diff hOto
  obtain ⟨t2, ht2⟩ := hS'c.elim_finite_subcover (fun x => X.π '' (Uq x ∩ X.PObj.boundaryᶜ))
    (fun x => hπo _ ((hUqo x).inter hbo)) (by
      intro z hz
      obtain ⟨⟨x, hxS, rfl⟩, hxOt⟩ := hz
      have hxb : x ∉ X.PObj.boundary := fun hxb => hxOt (hUbOt x (hSUb ⟨hxS, hxb⟩))
      exact mem_iUnion.2 ⟨x, x, ⟨hxUq x, hxb⟩, rfl⟩)
  set O2 : Set X.OrbitSpace := ⋃ x ∈ t2, X.π '' (Uq x ∩ X.PObj.boundaryᶜ) with hO2
  have hO2o : IsOpen O2 := isOpen_biUnion fun x _ => hπo _ ((hUqo x).inter hbo)
  -- `V` with `|V| ∩ ∂X = U_∂`
  obtain ⟨W', hW'o, rfl⟩ := hUb
  set OV : Set X.OrbitSpace := X.π '' W' ∪ X.π '' X.PObj.boundaryᶜ with hOV
  have hOVo : IsOpen OV := (hπo _ hW'o).union (hπo _ hbo)
  refine ⟨X.π ⁻¹' ((Ot ∪ O2) ∩ OV), ((hOto.union hO2o).inter hOVo).preimage X.continuous_π,
    ?_, ?_, ?_, ?_⟩
  · change X.π ⁻¹' (X.π '' (X.π ⁻¹' _)) = X.π ⁻¹' _
    rw [image_preimage_eq _ X.surjective_π]
  · intro x hxS
    refine ⟨?_, ?_⟩
    · by_cases hxt : X.π x ∈ Ot
      · exact Or.inl hxt
      · exact Or.inr (ht2 ⟨⟨x, hxS, rfl⟩, hxt⟩)
    · by_cases hxb : x ∈ X.PObj.boundary
      · exact Or.inl ⟨x, (hSUb ⟨hxS, hxb⟩).1, rfl⟩
      · exact Or.inr ⟨x, hxb, rfl⟩
  · ext x
    constructor
    · rintro ⟨⟨-, hxV⟩, hxb⟩
      rcases hxV with ⟨w, hw, hwx⟩ | ⟨w, hw, hwx⟩
      · have hwb : w ∈ X.PObj.boundary := EpGroupoid.mem_of_π_mem_image hbs ⟨x, hxb, hwx.symm⟩
        exact EpGroupoid.mem_of_π_mem_image hUbs ⟨w, ⟨hw, hwb⟩, hwx⟩
      · exact absurd (EpGroupoid.mem_of_π_mem_image hbs ⟨x, hxb, hwx.symm⟩) hw
    · rintro ⟨hxW, hxb⟩
      exact ⟨⟨Or.inl (hUbOt x ⟨hxW, hxb⟩), Or.inl ⟨x, hxW, rfl⟩⟩, hxb⟩
  · set T : Set X.OrbitSpace := (⋃ q ∈ t, X.π '' closure {y ∈ Uq q | B.AuxLe N (f y) 1}) ∪
      ⋃ x ∈ t2, X.π '' closure {y ∈ Uq x | B.AuxLe N (f y) 1} with hT
    have hTc : IsCompact T :=
      (t.isCompact_biUnion fun q _ => (hUqc q).image X.continuous_π).union
        (t2.isCompact_biUnion fun x _ => (hUqc x).image X.continuous_π)
    refine hTc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hTc.isClosed)
    rintro _ ⟨x, ⟨hxU, hxA⟩, rfl⟩
    rcases hxU.1 with (h1 | h2) | h3
    · obtain ⟨q, hq, u, huU, hux⟩ := mem_iUnion₂.1 h1
      have huA : u ∈ A := EpGroupoid.mem_of_π_mem_image hAs ⟨x, hxA, hux.symm⟩
      exact Or.inl (mem_iUnion₂.2 ⟨q, hq, u, subset_closure ⟨huU, huA⟩, hux⟩)
    · exact absurd ⟨x, hxA, rfl⟩ h2
    · obtain ⟨q, hq, u, huU, hux⟩ := mem_iUnion₂.1 h3
      have huA : u ∈ A := EpGroupoid.mem_of_π_mem_image hAs ⟨x, hxA, hux.symm⟩
      exact Or.inr (mem_iUnion₂.2 ⟨q, hq, u, subset_closure ⟨huU.1, huA⟩, hux⟩)

/-- **Theorem 12.4.6, pp. 590–592** (2017: Theorem 12.7): let `(P : W → X, μ)` be a strong bundle
over a tame ep-groupoid with paracompact orbit space and reflexive `(0, 1)`-fibres, `N` a
reflexive auxiliary norm, and `f` an sc-Fredholm section functor with compact solution set and the
reflexive local compactness property.  If `U_∂ ⊆ ∂X` is an open (in `∂X`) saturated neighbourhood
of `S_∂ = S_f ∩ ∂X` with `cl_{|X|}(|{y ∈ U_∂ | N(f(y)) ≤ 1}|)` compact, there is a saturated open
`U ⊇ S_f` with (1) `U ∩ ∂X = U_∂` and (2) `cl_{|X|}(|{x ∈ U | N(f(x)) ≤ 1}|)` compact.
Tameness, paracompactness and the Fredholm property beyond continuity are kept as in the text and
not used (`theorem_12_4_6_of_continuous`). -/
theorem theorem_12_4_6 (_hT : X.IsTame) (_hpara : X.HasParacompactOrbitSpace)
    (hB : E.HasReflexiveFibers) {N : B.One → ℝ} (hN : E.IsReflexiveAuxNorm N) {f : Obj → W}
    (hf : E.IsScFredholmSectionFunctor f) (hS : E.HasCompactSolutionSetEp f)
    (hlc : E.HasReflexiveLocalCompactnessEp f) {Ub : Set Obj}
    (hUb : ∃ W' : Set Obj, IsOpen W' ∧ Ub = W' ∩ X.PObj.boundary) (hUbs : X.IsSaturated Ub)
    (hSUb : solutionSet P f ∩ X.PObj.boundary ⊆ Ub)
    (hcpt : IsCompact (closure (X.π '' {y ∈ Ub | B.AuxLe N (f y) 1}))) :
    ∃ U : Set Obj, IsOpen U ∧ X.IsSaturated U ∧ solutionSet P f ⊆ U ∧
      U ∩ X.PObj.boundary = Ub ∧ IsCompact (closure (X.π '' {x ∈ U | B.AuxLe N (f x) 1})) := by
  obtain ⟨hsm, hfun⟩ := hf.1
  exact theorem_12_4_6_of_continuous hB hN hsm.1 (continuousOn_univ.1 hsm.2.continuousOn) hfun
    hS (hlc N hN) hUb hUbs hSUb hcpt

end EpStrongBundle

end Compactness

end Polyfold
