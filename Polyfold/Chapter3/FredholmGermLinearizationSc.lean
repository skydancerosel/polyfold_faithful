import Polyfold.Chapter1.ScFredholmCriterion
import Polyfold.Chapter3.FredholmGermIndex
import Polyfold.Chapter3.GoodPositionGerm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Proposition 3.52 in sc form**: the linearization of an sc-Fredholm section at a zero is an
**sc-Fredholm operator** (on all levels, Definition 1.8), with the sc form of **Proposition 3.5**
it rests on, and the clause "**`f'(x₀)` is sc-Fredholm**" of **Theorem 3.19**.  Round-trip items
V3.46, V3.68, V3.96 (Findings, Chapter 3, items 224 and 233–236).

# The linearization of an sc-Fredholm germ is sc-Fredholm

## The text, paraphrased

(Proposition 3.52) If `f` is an sc-Fredholm section of the tame strong bundle `P : Y → X` and
`f(x) = 0`, then `Tf(x) : T_xX → Y_x` is an sc-Fredholm operator.  Proof: in the chart of the
sc-Fredholm germ, `D(g − s)(0)` is sc-Fredholm by Proposition 3.10, `Dg(0)` by Proposition 1.10
(`Ds(0)` is sc⁺), and `Tf̃(0) : T₀O → K₀` is sc-Fredholm of index `ind Dg(0)` by Proposition 3.5.
(Proposition 3.5 (2)) `Tf(0)` is Fredholm iff `Dg(0)` is, with the same index.  (Theorem 3.19)
"`f'(x₀)` is an sc-Fredholm operator" (with `f'(x₀)` surjective).

## What is formalized

* `Polyfold.ScBanach.levelSubZeroEquiv` (`A₀ = A`) and
  `Polyfold.ScOperator.isFredholm_restrict_zero`: the level-`0` map of `ScOperator.restrict`
  (`ScFredholmCriterion.lean`) is a bounded operator `A → B` read through `A₀ = A`, `B₀ = B`, so
  its Fredholm property and index are those of that operator.
* `Polyfold.ConjugationData.scDeriv_isRegularizing_wholeChart` and
  `Polyfold.ConjugationData.scDeriv_isScFredholm_wholeChart`: for `k` sc-smooth with `k(0) = 0` conjugated
  to a basic germ `h` by `Ψ` (covering `ψ`), `Dk(0)` is an sc-operator, regularizing (from
  `Γ(0)Dk(0) = Dh(0)Dψ(0)`: `Γ(0)` preserves the levels, `Dh(0)` is regularizing by Propositions
  3.10 and 1.9, `Dψ(0)⁻¹ = Dψ'(0)` is an sc-operator), hence sc-Fredholm of index
  `dim Pn − dim Q` (the criterion `isScFredholm_of_isRegularizing`).
* `Polyfold.StrongRetr.isScOperator_scDeriv_r`, `StrongRetr.isScSubspace_range_scDeriv_r`
  (`T₀O = Dr(0)E` is an sc-subspace: `Dr(0)` is an sc-operator projection) and
  `StrongRetr.isScOperator_ρCLM`, `StrongRetr.isScSubspace_range_ρCLM` (`K₀ = ρ(0)F` is an
  sc-subspace: `ρ(0)` preserves the levels by Definition 2.47, is bounded on each by the closed
  graph theorem, and is a projection at `0 ∈ O`).
* `Polyfold.IsFillerOf.proposition_3_5_sc` (**Proposition 3.5, sc form**): for a filler `g` with
  `g(0) = 0` and `Dg(0)` an sc-Fredholm sc-operator, `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀` is an
  sc-Fredholm operator between the induced sc-Banach spaces, of index `ind Dg(0)` on every level.
* `Polyfold.proposition_3_52_local_sc_wholeChart` (in the chart of Definition 3.11, for conjugation data `d`
  of `g − s`) and `Polyfold.proposition_3_52_sc_wholeChart` (for a section of a strong bundle, in the chart
  of the germ data at the zero): **`Dg(0) : E → F` and `Tf(x₀) = Dg(0)|_{T₀O} : T₀O → K₀` are
  sc-Fredholm operators**, Fredholm on every level of index `dim d.Pn − dim d.Q` for every
  conjugation `d`.
* `Polyfold.theorem_3_19_linearization_sc_wholeChart` (**Theorem 3.19, "`f'(x₀)` is sc-Fredholm"**): the
  same at a zero in good position, and `Tf(x₀)` is onto on every level.

## What the text leaves implicit, and the choices made (the findings)

* **Proposition 3.5 in sc form needs condition (3) of the filler on level `0` only**, as the text
  states it: the sc-structure of `Tf(0)` on the higher levels comes from the regularity of the
  sc-Fredholm `Dg(0)` (`T₀O ∩ E_m = (T₀O)_m`), not from the filler.  Only the direction
  "`Dg(0)` sc-Fredholm ⟹ `Tf(0)` sc-Fredholm" is proved (the one Proposition 3.52 uses).
* **"`Dk(0)` is sc-Fredholm"** for the conjugate `k = g − s` of a basic germ is not literally in
  the text (Proposition 3.10 is about `h`); the text treats the conjugation as an identification.
  Here it is the criterion applied to `Dk(0) = Γ(0)⁻¹Dh(0)Dψ(0)`.  The level-preservation of
  `Γ(0)` and of `ρ(0)` is the filtration condition of Definition 2.47 at the smooth point `0`; the
  boundedness of `ρ(0) : F_m → F_m` (Definition 1.3 asks for it) is the closed graph theorem.
* The linearization `Tf(x₀)` is represented, as in `proposition_3_52_wholeChart`, in the strong bundle chart
  of the germ data centred at `x₀`: `T₀O = range Dr(0)`, `K₀ = range ρ(0)` with the induced
  sc-structures (`ScBanach.ofSubspace`), and `Tf(x₀)` the sc-operator `ScOperator.restrict` of
  `Dg(0)`, whose level-`0` map is `Dg(0)|_{T₀O}` (= `fillerRestrict`).  The statement in every
  chart around `x₀` (the round-trip's blind form of V3.46) is not proved here: the chart
  independence of the linearization is known on level `0` only
  (`StrongBundle.linAt_chart_independence`).
* No hypothesis beyond the text's is needed; the tameness of the bundle is not used.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### The level-`0` map of a restriction -/

/-- `A₀ = A`: level `0` of the sc-subspace `A` with its induced structure is `A`. -/
def ScBanach.levelSubZeroEquiv (E : ScBanach) (A : Submodule ℝ (E 0)) :
    E.levelSub A 0 ≃L[ℝ] A :=
  ContinuousLinearEquiv.equivOfInverse
    ((E.levelSub A 0).subtypeL.codRestrict A fun x => x.2)
    (A.subtypeL.codRestrict (E.levelSub A 0) fun x => x.2) (fun _ => rfl) (fun _ => rfl)

@[simp] lemma ScBanach.levelSubZeroEquiv_apply_coe (E : ScBanach) (A : Submodule ℝ (E 0))
    (x : E.levelSub A 0) : ((E.levelSubZeroEquiv A x : A) : E 0) = x := rfl

@[simp] lemma ScBanach.levelSubZeroEquiv_symm_apply_coe (E : ScBanach) (A : Submodule ℝ (E 0))
    (x : A) : (((E.levelSubZeroEquiv A).symm x : E.levelSub A 0) : E 0) = x := rfl

/-- **The level-`0` map of the restriction `A → B` of an sc-operator** is a bounded operator
`L : A → B` with `L x = T x`, read through `A₀ = A` and `B₀ = B`: if `L` is Fredholm, so is the
level-`0` map of `ScOperator.restrict`, with the index of `L`. -/
theorem ScOperator.isFredholm_restrict_zero (T : ScOperator E F) {A : Submodule ℝ (E 0)}
    {B : Submodule ℝ (F 0)} (hA : E.IsScSubspace A) (hB : F.IsScSubspace B)
    (hAB : ∀ x ∈ A, T 0 x ∈ B) {L : ↥A →L[ℝ] ↥B} (hL : ∀ x : A, (L x : F 0) = T 0 x)
    (hLF : L.IsFredholm) :
    (T.restrict hA hB hAB 0).IsFredholm ∧
      fredholmIndex (T.restrict hA hB hAB 0) = fredholmIndex L := by
  set e₁ : (E.ofSubspace hA) 0 ≃L[ℝ] A := E.levelSubZeroEquiv A with he₁
  set e₂ : B ≃L[ℝ] (F.ofSubspace hB) 0 := (F.levelSubZeroEquiv B).symm with he₂
  have heq : T.restrict hA hB hAB 0 = (e₂ : B →L[ℝ] (F.ofSubspace hB) 0).comp
      (L.comp (e₁ : (E.ofSubspace hA) 0 →L[ℝ] A)) := by
    refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    change T 0 x.1 = (L (e₁ x) : F 0)
    rw [hL]
    rfl
  rw [heq]
  exact isFredholm_equiv_comp_equiv hLF e₁ e₂

/-! ### The derivative of a map conjugated to a basic germ is sc-Fredholm -/

section Conjugate

variable {C U : Set (E 0)}

/-- `(0 : E₁)` is a smooth point. -/
lemma ScBanach.zero_mem_smoothLvl_one (E : ScBanach) : (0 : E 1) ∈ E.smoothLvl 1 := by
  change E.toBase 1 0 ∈ (E.smooth : Set (E 0))
  rw [map_zero]; exact E.smooth.zero_mem

/-- **The derivative of a map conjugated to a basic germ is regularizing**: if `k : U → F` is
sc-smooth with `k(0) = 0` and `(Ψ(u, k(u)))₂ = h(ψ(u))` near `0` for a basic germ `h` and a strong
bundle isomorphism `Ψ` covering `ψ`, then `Dk(0)e ∈ F_m` implies `e ∈ E_m`.  From
`Γ(0)Dk(0) = Dh(0)Dψ(0)` (as in `ConjugationData.scDeriv_isFredholm_index_wholeChart`): `Γ(0)` maps `F_m`
into `F'_m` (Definition 2.47 at the smooth point `0`), `Dh(0)` is regularizing (Propositions 3.10
and 1.9), and `Dψ(0)⁻¹ = Dψ'(0)` is an sc-operator (`ψ'` sc-smooth, `0` smooth). -/
theorem ConjugationData.scDeriv_isRegularizing_wholeChart (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) {k : E 0 → F 0} (hk : IsScSmooth U k) (hk0 : k 0 = 0)
    (d : ConjugationData U k) :
    ∀ (m : ℕ) (e : E 0), scDeriv U k 0 e ∈ range (F.toBase m) → e ∈ range (E.toBase m) := by
  obtain ⟨Pn, Q, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh, hev⟩ := d
  have hC : IsQuadrantLike E C := hU.isPartialQuadrant.isQuadrantLike
  have hC' : IsQuadrantLike (ScBanach.paramProd Pn W) (Ct ×ˢ univ) :=
    hU'.isPartialQuadrant.isQuadrantLike
  have hU'C : U' ⊆ Ct ×ˢ univ := by
    obtain ⟨Uo, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := hψ0 ▸ hΨ.toFun.base_mem h0
  have h01' : (0 : (ScBanach.paramProd Pn W) 1) ∈ (ScBanach.paramProd Pn W).lvlSet U' 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U'
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  have hψ'0 : ψ' 0 = 0 := hΨ.base_zero' h0 hψ0
  have hψsm : IsScSmooth U ψ := hΨ.toFun.base_isScSmooth hU
  have hψ'sm : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψU' : MapsTo ψ U U' := fun u hu => hΨ.toFun.base_mem hu
  set Dk := scDeriv U k 0 with hDk
  set Dψ := scDeriv U ψ 0 with hDψ
  set Dψ' := scDeriv U' ψ' 0 with hDψ'
  set Dh := scDerivGerm (F := ScBanach.paramProd Q W) G h 0 with hDh
  set Γ := hΨ.toFun.fiberCLM h0 with hΓ
  -- (a) `Dh(0)` is sc-Fredholm, hence regularizing
  obtain ⟨hDhop, hDhF, -⟩ := proposition_3_10_basic hCt hh
  -- (b) `Γ(0)Dk(0) = Dh(0)Dψ(0)`
  have hlhs : scDeriv U (fun u => (Ψ (u, k u)).2) 0 = Γ.comp Dk :=
    hΨ.toFun.scDeriv_fiber_comp hU h0 hk hk0
  have hlevψ : levelMap ψ 1 (0 : E 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hψ0])
  have hrhs : scDeriv U (fun u => (Ψ (u, k u)).2) 0 = Dh.comp Dψ := by
    obtain ⟨N₁, hN₁sub, hN₁open, h0N₁⟩ := mem_nhds_iff.1 hev
    have hU₁ : IsRelOpenInQuadrant E C (U ∩ N₁) := hU.inter_isOpen hN₁open
    have h0₁ : (0 : E 0) ∈ U ∩ N₁ := ⟨h0, h0N₁⟩
    set G₀ := ScNbhdGerm.ofSet hU₁.relOpen h0₁ with hG₀
    have hψG₀ : IsSc0Germ (F := ScBanach.paramProd Pn W) G₀ ψ :=
      ((hψsm.of_subset hU₁.isScDomain inter_subset_left).isScSmoothGerm hC hU₁.relOpen h0₁) 0
    have hψC' : MapsTo ψ (G₀.U 0) (Ct ×ˢ univ) := fun u hu => hU'C (hψU' hu.1)
    set G₁ := G₀.preimage G hψG₀ hψ0 hψC' with hG₁
    have hG₁sub : ∀ m, G₁.U m ⊆ (ScNbhdGerm.ofSet hU.relOpen h0).U m := fun m x hx =>
      E.lvlSet_mono inter_subset_left m (G₀.preimage_subset G hψG₀ hψ0 hψC' m hx)
    have hhG : IsSc1GermWith (F := ScBanach.paramProd Q W) G h
        (scDerivGerm (F := ScBanach.paramProd Q W) G h) :=
      (hh.isScSmooth 1).1.isSc1GermWith_scDerivGerm
    have hbridge : ∀ {F₁ : ScBanach} {φ : E 0 → F₁ 0}, IsSc1 U φ →
        IsSc1GermWith (ScNbhdGerm.ofSet hU.relOpen h0) φ (scDeriv U φ) := fun {F₁ φ} hφ =>
      ⟨hφ.isSc0.isSc0Germ hU.relOpen h0, hφ.isSc1With_scDeriv.hasFDerivWithinAt, by
        have := hφ.tangentMap_isSc0
        rw [ScNbhdGerm.ofSet_tangent]
        exact this.isSc0Germ _ _⟩
    have hψG₁ : IsSc1GermWith (F := ScBanach.paramProd Pn W) G₁ ψ (scDeriv U ψ) :=
      (hbridge hψsm.isSc1).mono hG₁sub
    have hcomp : IsSc1GermWith (F := ScBanach.paramProd Q W) G₁ (h ∘ ψ)
        (fun x => (scDerivGerm (F := ScBanach.paramProd Q W) G h (levelMap ψ 1 x)).comp
          (scDeriv U ψ x)) :=
      hhG.comp (G.relOpenConvex hC' 1) hψG₁ (G₀.preimage_mapsToGerm G hψG₀ hψ0 hψC')
    have hUF := (hU.prod_univ F).isScDomain
    have hpairsm : IsScSmooth U (scPair (_root_.id : E 0 → E 0) k) :=
      (isScSmooth_id hU.isScDomain).scPair hU.isScDomain hk
    have hksm : IsScSmooth U fun u => (Ψ (u, k u)).2 :=
      (IsScSmooth.comp hU.isScDomain hUF (hΨ.toFun.isScSmooth_zero.snd hUF) hpairsm
        fun u hu => ⟨hu, mem_univ _⟩).congr hU.isScDomain fun _ _ => rfl
    have hkG₁ : IsSc1GermWith G₁ (h ∘ ψ) (scDeriv U fun u => (Ψ (u, k u)).2) :=
      ((hbridge hksm.isSc1).mono hG₁sub).congr fun u hu => by
        have hu' : u ∈ U ∩ N₁ := G₀.preimage_subset G hψG₀ hψ0 hψC' 0 hu
        exact hN₁sub hu'.2 hu'.1
    have e1 := IsSc1Germ.scDerivGerm_eqOn hC hkG₁ (G₁.zero_mem 1)
    have e2 := IsSc1Germ.scDerivGerm_eqOn hC hcomp (G₁.zero_mem 1)
    rw [← e1, e2, hlevψ]
  have hkey : Γ.comp Dk = Dh.comp Dψ := by rw [← hlhs, hrhs]
  -- (c) `Dψ'(0)Dψ(0) = 1`, and `Dψ'(0)` is an sc-operator
  have hψψ'D : ∀ x, Dψ' (Dψ x) = x := fun x => by
    have := scDeriv_comp_eq_self hU hU' hψsm.isSc1 hψ'sm.isSc1 hψU' hψψ' h01 x
    rwa [hlevψ] at this
  have hDψ'op : IsScOperator Dψ' :=
    hψ'sm.isSc1.isSc1With_scDeriv.scOperator_deriv h01'
      (ScBanach.paramProd Pn W).zero_mem_smoothLvl_one
  -- (d) the regularity
  intro m e he
  have hΓe : Γ (Dk e) ∈ range ((ScBanach.paramProd Q W).toBase m) := by
    obtain ⟨y, hy⟩ := he
    have := (hΨ.toFun.preserves_filtration m m (Nat.le_succ m) 0 h0 ⟨0, map_zero _⟩ (Dk e)
      ⟨y, hy⟩).2
    rwa [hΓ, IsStrongBundleMap.fiberCLM_apply]
  have hDhe : hDhop.toScOperator 0 (Dψ e) ∈ range ((ScBanach.paramProd Q W).toBase m) := by
    rw [hDhop.toScOperator_zero]
    have := congrArg (fun T : E 0 →L[ℝ] (ScBanach.paramProd Q W) 0 => T e) hkey
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [← this]; exact hΓe
  obtain ⟨z, hz⟩ := hDhF.isRegularizing m (Dψ e) hDhe
  obtain ⟨Tm, hTm⟩ := hDψ'op m
  exact ⟨Tm z, by rw [hTm, hz, hψψ'D]⟩

/-- **The derivative of a map conjugated to a basic germ is sc-Fredholm**, of index
`n − N = dim Pn − dim Q`: `Dk(0)` is an sc-operator (`k` sc-smooth, `0` smooth), Fredholm on
level `0` of index `n − N` (`ConjugationData.scDeriv_isFredholm_index_wholeChart`) and regularizing
(`ConjugationData.scDeriv_isRegularizing_wholeChart`); the criterion `isScFredholm_of_isRegularizing`.  The
text's "`D(g − s)(0)` is sc-Fredholm by Proposition 3.10" (proof of Proposition 3.52; round-trip
item V3.46, Findings, Chapter 3, item 235). -/
theorem ConjugationData.scDeriv_isScFredholm_wholeChart (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) {k : E 0 → F 0} (hk : IsScSmooth U k) (hk0 : k 0 = 0)
    (d : ConjugationData U k) :
    ∃ hop : IsScOperator (scDeriv U k 0), IsScFredholm hop.toScOperator ∧
      scIndex hop.toScOperator = finrank ℝ d.Pn - finrank ℝ d.Q := by
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have hop : IsScOperator (scDeriv U k 0) :=
    hk.isSc1.isSc1With_scDeriv.scOperator_deriv h01 E.zero_mem_smoothLvl_one
  obtain ⟨hF, hind⟩ := d.scDeriv_isFredholm_index_wholeChart hU h0 hk hk0
  refine ⟨hop, isScFredholm_of_isRegularizing ?_ ?_, ?_⟩
  · rw [hop.toScOperator_zero]; exact hF
  · intro m e he
    rw [hop.toScOperator_zero] at he
    exact d.scDeriv_isRegularizing_wholeChart hU h0 hk hk0 m e he
  · rw [scIndex_eq_fredholmIndex, hop.toScOperator_zero, hind]

end Conjugate

/-! ### `T₀O` and `K₀` are sc-subspaces -/

namespace StrongRetr

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} (hU : IsRelOpenInQuadrant E C U)
  (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U)

include hU hR h0 in
/-- `Dr(0)` is an sc-operator (`r` sc-smooth, `0` smooth). -/
theorem isScOperator_scDeriv_r : IsScOperator (scDeriv U (r R) 0) := by
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  exact (r_isScSmooth hU hR).isSc1.isSc1With_scDeriv.scOperator_deriv h01
    E.zero_mem_smoothLvl_one

include hU hR in
/-- **`T₀O = Dr(0)E` is an sc-subspace** (`0 ∈ O`): `Dr(0)` is an sc-operator with
`Dr(0)² = Dr(0)`, so `E = Dr(0)E ⊕ ker Dr(0)` is an sc-splitting (Lemma 2.B). -/
theorem isScSubspace_range_scDeriv_r (h0O : (0 : E 0) ∈ r R '' U) :
    E.IsScSubspace (rangeS (scDeriv U (r R) 0)) := by
  have hop := isScOperator_scDeriv_r hU hR (mem_U_of_mem_O hR h0O)
  have hidem : ∀ x, hop.toScOperator 0 (hop.toScOperator 0 x) = hop.toScOperator 0 x := by
    rw [hop.toScOperator_zero]; exact scDeriv_r_idem hU hR h0O
  have h := ScBanach.isScSplitting_of_idem hop.toScOperator hidem
  rw [hop.toScOperator_zero] at h
  exact h.1

include hR h0 in
/-- **`ρ(0)` is an sc-operator**: it maps `F_m` into `F_m` (the filtration condition of
Definition 2.47 at the smooth point `0`), and is then bounded on every level by the closed graph
theorem (`isScOperator_of_mapsTo`). -/
theorem isScOperator_ρCLM : IsScOperator (ρCLM hR h0) :=
  isScOperator_of_mapsTo fun m x =>
    (hR.preserves_filtration m m (Nat.le_succ m) 0 h0 ⟨0, map_zero _⟩ (F.toBase m x) ⟨x, rfl⟩).2

include hR in
/-- **`K₀ = ρ(0)F` is an sc-subspace** (`0 ∈ O`): `ρ(0)` is an sc-operator with `ρ(0)² = ρ(0)`
(Lemma 2.B). -/
theorem isScSubspace_range_ρCLM (h0O : (0 : E 0) ∈ r R '' U) :
    F.IsScSubspace (rangeS (ρCLM hR h0)) := by
  have hop := isScOperator_ρCLM hR h0
  have hidem : ∀ x, hop.toScOperator 0 (hop.toScOperator 0 x) = hop.toScOperator 0 x := by
    rw [hop.toScOperator_zero]; exact ρCLM_idem hR h0 h0O
  have h := ScBanach.isScSplitting_of_idem hop.toScOperator hidem
  rw [hop.toScOperator_zero] at h
  exact h.1

end StrongRetr

/-! ### Proposition 3.5 in sc form -/

open StrongRetr

namespace IsFillerOf

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {hU : IsRelOpenInQuadrant E C U}
  {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {fb g : E 0 → F 0}
  (hfg : IsFillerOf hU hR h0 fb g)

include hfg in
/-- **Proposition 3.5, sc form** (the direction used by Proposition 3.52): let `g` fill `f` with
`g(0) = 0` (`f` a section of `K → O`, `0 ∈ O`), and let `Dg(0) : E → F` be an sc-Fredholm
sc-operator.  Then `T₀O = Dr(0)E` and `K₀ = ρ(0)F` are sc-subspaces, `Dg(0)` maps `T₀O` into
`K₀`, and `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀` (`ScOperator.restrict`, level `0`: `fillerRestrict`)
is an sc-Fredholm operator, Fredholm on every level of index `ind Dg(0)`.  Only condition (3) of
the filler **on level `0`** is used (through Proposition 3.5 on level `0`); the higher levels come
from the regularity of `Dg(0)` (`IsScFredholm.restrict`).  Findings, Chapter 3, item 234. -/
theorem proposition_3_5_sc (hg : IsScSmooth U g) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) (hDg : IsScOperator (scDeriv U g 0))
    (hDgF : IsScFredholm hDg.toScOperator) :
    ∃ (hT : E.IsScSubspace (rangeS (scDeriv U (r R) 0)))
      (hK : F.IsScSubspace (rangeS (ρCLM hR h0)))
      (hTK : ∀ x ∈ rangeS (scDeriv U (r R) 0), hDg.toScOperator 0 x ∈ rangeS (ρCLM hR h0)),
      IsScFredholm (hDg.toScOperator.restrict hT hK hTK) ∧
      (∀ x : (E.ofSubspace hT) 0,
        ((hDg.toScOperator.restrict hT hK hTK 0 x).1 : F 0) = scDeriv U g 0 x.1) ∧
      ∀ m, ((hDg.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
        fredholmIndex ((hDg.toScOperator.restrict hT hK hTK) m) =
          fredholmIndex (scDeriv U g 0) := by
  obtain ⟨h1, -, hFiff, hindeq⟩ := hfg.proposition_3_5 hg hg0 h0O hfK
  have hT := isScSubspace_range_scDeriv_r hU hR h0O
  have hK := isScSubspace_range_ρCLM hR h0 h0O
  have hTK : ∀ x ∈ rangeS (scDeriv U (r R) 0), hDg.toScOperator 0 x ∈ rangeS (ρCLM hR h0) := by
    rintro _ ⟨y, rfl⟩
    rw [hDg.toScOperator_zero]
    exact ⟨_, h1 y⟩
  have hDgF0 : (scDeriv U g 0).IsFredholm := by
    have := (hDgF.fredholmIndex_lvl 0).1
    rwa [hDg.toScOperator_zero] at this
  obtain ⟨hF0, hind0⟩ := hDg.toScOperator.isFredholm_restrict_zero hT hK hTK
    (L := fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1)
    (fun x => by rw [fillerRestrict_apply, hDg.toScOperator_zero]) (hFiff.2 hDgF0)
  obtain ⟨hsc, hlvl⟩ := hDgF.restrict hF0
  refine ⟨hT, hK, hTK, hsc, fun x => ?_, fun m => ?_⟩
  · change hDg.toScOperator 0 x.1 = _
    rw [hDg.toScOperator_zero]
  · rw [← hindeq, ← hind0]
    exact hlvl m

end IsFillerOf

/-! ### Proposition 3.52 in sc form -/

section Prop352

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **Proposition 3.52 in the chart of Definition 3.11, sc form** (round-trip items V3.46,
V3.68): let `g` be a filled version of the principal part `f̂` of a section at a zero
(`f̂(0) = 0`), `s` a local sc⁺-section with `s(0) = g(0)` and `d` conjugation data of `g − s` to a
basic germ `h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ ℝⁿ`.  Then `Dg(0) : E → F` is an **sc-Fredholm
operator**, `T₀O = Dr(0)E` and `K₀ = ρ(0)F` are sc-subspaces, and `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀`
(`ScOperator.restrict`) is an **sc-Fredholm operator**; on every level both are Fredholm of index
`n − N = dim d.Pn − dim d.Q`.  The text's proof: `D(g − s)(0)` is sc-Fredholm
(`ConjugationData.scDeriv_isScFredholm_wholeChart`, from Proposition 3.10), `Dg(0)` by Proposition 1.10
(`Ds(0)` is sc⁺), `Tf(0)` by Proposition 3.5 (`IsFillerOf.proposition_3_5_sc`). -/
theorem proposition_3_52_local_sc_wholeChart (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFilledVersion hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {s : E 0 → F 1}
    (hs : IsScSmooth (F := F.shift) U s) (hs0 : F.toBase 1 (s 0) = g 0)
    (d : ConjugationData U fun u => g u - F.toBase 1 (s u)) :
    ∃ (hDg : IsScOperator (scDeriv U g 0)) (hT : E.IsScSubspace (rangeS (scDeriv U (r R) 0)))
      (hK : F.IsScSubspace (rangeS (ρCLM hR h0)))
      (hTK : ∀ x ∈ rangeS (scDeriv U (r R) 0), hDg.toScOperator 0 x ∈ rangeS (ρCLM hR h0)),
      IsScFredholm hDg.toScOperator ∧ IsScFredholm (hDg.toScOperator.restrict hT hK hTK) ∧
      (∀ x : (E.ofSubspace hT) 0,
        ((hDg.toScOperator.restrict hT hK hTK 0 x).1 : F 0) = scDeriv U g 0 x.1) ∧
      ∀ m, (hDg.toScOperator m).IsFredholm ∧
        fredholmIndex (hDg.toScOperator m) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        ((hDg.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
        fredholmIndex ((hDg.toScOperator.restrict hT hK hTK) m) =
          finrank ℝ d.Pn - finrank ℝ d.Q := by
  have hg : IsScSmooth U g := hfill.isScSmooth
  have hg0 : g 0 = 0 := by rw [← hfill.filler.eq_on.self_of_nhds h0O, hfb0]
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have huniq := hU.isScDomain.uniqueDiffWithinAt 1 0 h01
  -- `k = g − s` (written out: `d` depends on it) has an sc-Fredholm derivative
  have hk : IsScSmooth U fun u => g u - F.toBase 1 (s u) :=
    hg.sub hU.isScDomain (hs.toBase_shift hU.isScDomain)
  have hk0 : (fun u => g u - F.toBase 1 (s u)) 0 = 0 := by
    change g 0 - F.toBase 1 (s 0) = 0
    rw [hs0, hg0, sub_self]
  obtain ⟨hDkop, hDkF, hDkind⟩ := d.scDeriv_isScFredholm_wholeChart hU h0 hk hk0
  -- `Dg(0) = Dk(0) + ιDs(0)`, `Ds(0)` an sc⁺-operator
  have hDsop : IsScOperator (scDeriv (F := F.shift) U s 0) :=
    hs.isSc1.isSc1With_scDeriv.scOperator_deriv h01 E.zero_mem_smoothLvl_one
  set S : ScPlus E F := hDsop.toScOperator with hS
  have hDg : scDeriv U g 0 =
      scDeriv U (fun u => g u - F.toBase 1 (s u)) 0 + S.toScOperator 0 := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
    have h1 := hg.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01
    have h2 := (hk.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01).add
      ((F.toBase 1).hasFDerivAt.comp_hasFDerivWithinAt (0 : E 1)
        (hs.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01))
    have h2' : HasFDerivWithinAt (g ∘ E.toBase 1)
        ((scDeriv U (fun u => g u - F.toBase 1 (s u)) 0).comp (E.toBase 1) +
          (F.toBase 1).comp ((scDeriv (F := F.shift) U s 0).comp (E.toBase 1)))
        (E.lvlSet U 1) 0 := by
      refine h2.congr (fun x _ => ?_) ?_
      · simp only [Function.comp_apply, Pi.add_apply]; abel
      · simp only [Function.comp_apply, Pi.add_apply]; abel
    have := huniq.eq h1 h2'
    rw [this, ContinuousLinearMap.add_comp]
    congr 1
    ext x
    change F.toBase 1 (scDeriv (F := F.shift) U s 0 (E.toBase 1 x)) = F.incl 0 (S 0 (E.toBase 1 x))
    rw [hS, hDsop.toScOperator_zero]
    rfl
  have hDgop : IsScOperator (scDeriv U g 0) :=
    hg.isSc1.isSc1With_scDeriv.scOperator_deriv h01 E.zero_mem_smoothLvl_one
  have heqop : hDgop.toScOperator = hDkop.toScOperator + S.toScOperator := by
    apply ScOperator.ext_base
    ext x
    rw [ScOperator.add_apply, hDgop.toScOperator_zero, hDkop.toScOperator_zero, hDg]
    rfl
  -- Proposition 1.10
  have hDgF : IsScFredholm hDgop.toScOperator := heqop ▸ proposition_1_10 hDkF S
  have hDgind : scIndex hDgop.toScOperator = finrank ℝ d.Pn - finrank ℝ d.Q := by
    rw [heqop, proposition_1_10_index hDkF S, hDkind]
  -- Proposition 3.5
  obtain ⟨hT, hK, hTK, hTF, happ, hTlvl⟩ :=
    hfill.filler.proposition_3_5_sc hg hg0 h0O hfK hDgop hDgF
  refine ⟨hDgop, hT, hK, hTK, hDgF, hTF, happ, fun m => ?_⟩
  obtain ⟨hDgFm, hDgindm⟩ := hDgF.fredholmIndex_lvl m
  obtain ⟨hTFm, hTindm⟩ := hTlvl m
  have h0ind : fredholmIndex (scDeriv U g 0) = finrank ℝ d.Pn - finrank ℝ d.Q := by
    rw [← hDgop.toScOperator_zero, ← scIndex_eq_fredholmIndex, hDgind]
  exact ⟨hDgFm, hDgindm.trans hDgind, hTFm, hTindm.trans h0ind⟩

end Prop352

/-! ### Proposition 3.52 for sections of strong bundles, sc form -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **Proposition 3.52, sc form** (round-trip items V3.46, V3.68; Findings, Chapter 3, item 224):
let `f` be a section of the strong bundle `P : Y → X` with `(f, x₀)` an sc-Fredholm germ and
`f(x₀) = 0`.  In the strong bundle chart of Definition 3.11 centred at `x₀`, with the filled
version `g` of the principal part `f̂` and the local sc⁺-section `s` (`s(0) = g(0)`) for which
`g − s` is conjugated to a basic germ, `Dg(0) : E → F` and the linearization
`Tf(x₀) = Dg(0)|_{T₀O} : T₀O → K₀` (`T₀O = Dr(0)E`, `K₀ = ρ(0)F` sc-subspaces with the induced
sc-structures) are **sc-Fredholm operators**, and for **every** conjugation `d` of `g − s` to a
basic germ `h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ ℝⁿ`, their level maps all have index
`n − N = dim d.Pn − dim d.Q`.  (The text: "`Tf(x) : T_xX → Y_x` is an sc-Fredholm operator"; the
level-`0` statement is `proposition_3_52_index_wholeChart`.) -/
theorem proposition_3_52_sc_wholeChart (hf : IsSection P f) {x₀ : X} (hg : B.IsScFredholmGermWholeChart f x₀)
    (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1)
      (_ : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g)
      (_ : IsScSmooth (F := c.F.shift) c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
      (_ : Nonempty (ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)))
      (hDg : IsScOperator (scDeriv c.U g 0))
      (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) 0)))
      (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction h0)))
      (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) 0),
        hDg.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction h0)),
      IsScFredholm hDg.toScOperator ∧ IsScFredholm (hDg.toScOperator.restrict hT hK hTK) ∧
      (∀ x : (c.φ.model.E.ofSubspace hT) 0,
        ((hDg.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) = scDeriv c.U g 0 x.1) ∧
      ∀ d : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u)), ∀ m,
        fredholmIndex (hDg.toScOperator m) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        fredholmIndex ((hDg.toScOperator.restrict hT hK hTK) m) =
          finrank ℝ d.Pn - finrank ℝ d.Q := by
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, s, hfill, hs, hs0, hconj⟩ := hg
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model x₀ hxV
  have hfb0 : c.principal f 0 = 0 := by
    have := (c.isZeroAt_iff hf hxV).1 hx₀
    rwa [hφ0] at this
  have hfK : ∀ x ∈ r c.R '' c.U, (x, c.principal f x) ∈ c.R '' (c.U ×ˢ univ) := by
    intro x hx
    rw [c.r_image] at hx
    rw [← c.apply_section hf hx]
    change c (f (c.φ.symm x)) ∈ c.K
    rw [← c.image_source]
    exact ⟨_, c.mem_source_of_proj (by rw [hf]; exact c.φ.symm_mapsTo hx), rfl⟩
  obtain ⟨d₀⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  obtain ⟨hDg, hT, hK, hTK, hDgF, hTF, happ, -⟩ :=
    proposition_3_52_local_sc_wholeChart c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hs hs0 d₀
  refine ⟨c, hc, hxV, hφ0, h0U, g, s, hfill, hs, hs0, ⟨d₀⟩, hDg, hT, hK, hTK, hDgF, hTF, happ,
    fun d m => ?_⟩
  obtain ⟨hDg', hT', hK', hTK', -, -, -, hlvl⟩ :=
    proposition_3_52_local_sc_wholeChart c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hs hs0 d
  obtain ⟨-, h1, -, h2⟩ := hlvl m
  exact ⟨h1, h2⟩

/-! ### Theorem 3.19: `f'(x₀)` is sc-Fredholm -/

/-- **Theorem 3.19, the first clause, sc form: "`f'(x₀)` is sc-Fredholm"** (round-trip item
V3.96; cf. `theorem_3_19_linearization_wholeChart`, `theorem_3_19_linearization_index_wholeChart`, which give the
level-`0` statements): for an sc-Fredholm section `f` and a zero `x₀` in good position (in the
interior case, the text's hypothesis "`f'(x₀)` surjective"), in the chart of Definition 3.53
centred at `x₀`, `Dg(0)` and `f'(x₀) = Tf(x₀) = Dg(0)|_{T₀O} : T₀O → K₀` are sc-Fredholm
operators, `Tf(x₀)` is onto on every level, and for every conjugation `d` of `g − s` to a basic
germ the level maps of both have index `dim d.Pn − dim d.Q`. -/
theorem theorem_3_19_linearization_sc_wholeChart (hf : B.IsScFredholmSectionWholeChart f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) (hg : B.IsGoodPositionGermWholeChart f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1)
      (_ : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g)
      (_ : IsScSmooth (F := c.F.shift) c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
      (_ : Nonempty (ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)))
      (hDg : IsScOperator (scDeriv c.U g 0))
      (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) 0)))
      (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction h0)))
      (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) 0),
        hDg.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction h0)),
      IsScFredholm hDg.toScOperator ∧ IsScFredholm (hDg.toScOperator.restrict hT hK hTK) ∧
      (∀ x : (c.φ.model.E.ofSubspace hT) 0,
        ((hDg.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) = scDeriv c.U g 0 x.1) ∧
      (∀ m, Surjective ((hDg.toScOperator.restrict hT hK hTK) m)) ∧
      ∀ d : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u)), ∀ m,
        fredholmIndex (hDg.toScOperator m) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        fredholmIndex ((hDg.toScOperator.restrict hT hK hTK) m) =
          finrank ℝ d.Pn - finrank ℝ d.Q := by
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, s, hfill, hs, hs0, hconj, hgp⟩ := hg
  have hfs : IsSection P f := hf.isScSmooth.1
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model x₀ hxV
  have hfb0 : c.principal f 0 = 0 := by
    have := (c.isZeroAt_iff hfs hxV).1 hx₀
    rwa [hφ0] at this
  have hfK : ∀ x ∈ r c.R '' c.U, (x, c.principal f x) ∈ c.R '' (c.U ×ˢ univ) := by
    intro x hx
    rw [c.r_image] at hx
    rw [← c.apply_section hfs hx]
    change c (f (c.φ.symm x)) ∈ c.K
    rw [← c.image_source]
    exact ⟨_, c.mem_source_of_proj (by rw [hfs]; exact c.φ.symm_mapsTo hx), rfl⟩
  have hg0 : g 0 = 0 := by rw [← hfill.filler.eq_on.self_of_nhds h0O, hfb0]
  obtain ⟨d₀⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  obtain ⟨hDg, hT, hK, hTK, hDgF, hTF, happ, -⟩ :=
    proposition_3_52_local_sc_wholeChart c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hs hs0 d₀
  -- `Tf(x₀)` is onto on level `0` (good position), hence on every level (regularizing)
  have h1 := hfill.filler.ρ_deriv_comp_r hfill.isScSmooth hg0 h0O hfK
  have hsurj0 : Surjective (hDg.toScOperator.restrict hT hK hTK 0) := by
    intro y
    obtain ⟨⟨x, hx⟩, hxy⟩ := hgp.surjective_fillerRestrict h1 ⟨y.1, y.2⟩
    exact ⟨⟨x, hx⟩, Subtype.ext ((happ _).trans (congrArg Subtype.val hxy))⟩
  refine ⟨c, hc, hxV, hφ0, h0U, g, s, hfill, hs, hs0, ⟨d₀⟩, hDg, hT, hK, hTK, hDgF, hTF, happ,
    hTF.isRegularizing.surjective hsurj0, fun d m => ?_⟩
  obtain ⟨hDg', hT', hK', hTK', -, -, -, hlvl⟩ :=
    proposition_3_52_local_sc_wholeChart c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hs hs0 d
  obtain ⟨-, h1, -, h2⟩ := hlvl m
  exact ⟨h1, h2⟩

end Bundle

end Polyfold
