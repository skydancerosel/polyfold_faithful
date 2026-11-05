import Polyfold.Chapter3.FredholmGermLinearization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Proposition 3.52 with its index clause**: the linearization of an sc-Fredholm section at a zero
is Fredholm of the index `n − N` of the basic germ to which the filled version is conjugated, with
`n` and `N` the dimensions of the conjugation data at hand (not "some natural numbers").

# The index in Proposition 3.52

## The text, paraphrased

(Proposition 3.52, with the proof of Theorem 3.54) If `f` is an sc-Fredholm section of the tame
strong bundle `P : Y → X` and `f(x) = 0`, then `Tf(x) : T_xX → Y_x` is an sc-Fredholm operator.
In the chart of Definition 3.11, `g − s` is conjugated to a basic germ
`h : O(([0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ) ⊕ W, 0) → (ℝᴺ ⊕ W, 0)`; `D(g − s)(0)` is sc-Fredholm of the index
`n − N` of `h` (Proposition 3.10), `Dg(0)` is an sc⁺-perturbation of it (Proposition 1.10), and
`Tf̃(0) = Dg(0)|_{T₀O} : T₀O → K₀` has the same index (Proposition 3.5).

## What is formalized

* `Polyfold.ConjugationData U k`: the witnesses of `IsConjugateToBasicGerm U k` (Definition 3.11,
  second paragraph) as a structure, so that the parameter space `Pn = ℝⁿ` and the
  finite-dimensional target `Q = ℝᴺ` of the basic germ can be named;
  `Polyfold.isConjugateToBasicGerm_iff_nonempty`.
* `Polyfold.ConjugationData.scDeriv_isFredholm_index_wholeChart`: for `k` sc-smooth with `k(0) = 0` and
  conjugation data `d` of `k`, `Dk(0)` is Fredholm (level `0`) of index `dim d.Pn − dim d.Q`;
  `Polyfold.ConjugationData.index_eq_wholeChart`: the number `dim d.Pn − dim d.Q` does not depend on the
  conjugation data.
* `Polyfold.proposition_3_52_local_index_wholeChart` (in the chart of Definition 3.11, for given conjugation
  data `d` of `g − s`) and `Polyfold.proposition_3_52_index_wholeChart` (for a section of a strong bundle):
  `Dg(0)` and `Tf(x₀) = Dg(0)|_{T₀O} : T₀O → K₀` are Fredholm with
  `ind Tf(x₀) = ind Dg(0) = dim d.Pn − dim d.Q` for **every** conjugation data `d` of `g − s` to a
  basic germ (and such data exist).

## What the text leaves implicit, and the choices made (the findings)

* **The index clause of `proposition_3_52_wholeChart` is vacuous.**  `proposition_3_52_local_wholeChart` and
  `proposition_3_52_wholeChart` (`FredholmGermLinearization.lean`, statements kept for their consumers) state
  the index as "`n − N` for some natural numbers `n`, `N`", which every integer is.  The content
  of the text's claim is that `n` and `N` are the dimensions of the conjugating basic germ; this
  needs the witnesses of `IsConjugateToBasicGerm`, which is an existential proposition, as data:
  `ConjugationData`.  The proofs are those of `FredholmGermLinearization.lean` with the
  dimensions carried along.
* **Independence of the conjugation.**  Since the index of `Dk(0)` is computed by every
  conjugation, `dim Pn − dim Q` is the same for all conjugations of `k` to basic germs
  (`ConjugationData.index_eq_wholeChart`); the text's "the Fredholm index is invariant under strong bundle
  isomorphisms" (after Theorem 3.38) is this statement for the conjugations of one germ.
* Only the level-`0` (classical) Fredholm property is proved here, as in `proposition_3_52_wholeChart`; the
  sc-Fredholm property of `Dg(0)` and `Tf(x)` on all levels, with the index `dim d.Pn − dim d.Q`
  on every level, is `proposition_3_52_local_sc_wholeChart` / `proposition_3_52_sc_wholeChart`
  (`FredholmGermLinearizationSc.lean`).
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### Conjugation data -/

section Conjugate

variable {C U : Set (E 0)}

/-- **The data of a conjugation to a basic germ** (Definition 3.11, second paragraph): the
witnesses of `IsConjugateToBasicGerm U k` as a structure, so that the dimensions `n = dim Pn`,
`N = dim Q` of the basic germ `h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ ℝⁿ`, can be named
(`isConjugateToBasicGerm_iff_nonempty`). -/
structure ConjugationData (U : Set (E 0)) (k : E 0 → F 0) where
  /-- The parameter space `ℝⁿ` of the basic germ. -/
  Pn : Type
  /-- The finite-dimensional part `ℝᴺ` of the target of the basic germ. -/
  Q : Type
  [i1 : NormedAddCommGroup Pn]
  [i2 : NormedSpace ℝ Pn]
  [i3 : FiniteDimensional ℝ Pn]
  [i4 : NormedAddCommGroup Q]
  [i5 : NormedSpace ℝ Q]
  [i6 : FiniteDimensional ℝ Q]
  /-- The fibre `W`. -/
  W : ScBanach
  /-- The partial quadrant `C̃ ⊆ ℝⁿ`. -/
  Ct : Set Pn
  /-- The domain `U'` of the push-forward, relatively open in `C̃ ⊕ W`. -/
  U' : Set ((ScBanach.paramProd Pn W) 0)
  /-- The strong bundle isomorphism `Ψ : U ◁ F → U' ◁ (ℝᴺ ⊕ W)`. -/
  Ψ : E 0 × F 0 → (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0
  /-- Its inverse. -/
  Ψ' : (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0 → E 0 × F 0
  /-- The germ of neighbourhoods of the basic germ. -/
  G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
  /-- The basic germ `h`. -/
  h : Pn × W 0 → Q × W 0
  /-- Its contraction map. -/
  Bc : Pn × W 0 → W 0
  quadrant : IsPartialQuadrant (ScBanach.const Pn) Ct
  relOpen : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U'
  iso : IsStrongBundleIso U U' Ψ Ψ'
  base_zero : IsStrongBundleMap.base Ψ 0 = 0
  germ_subset : G.U 0 ⊆ U'
  basic : IsBasicGerm Ct G h Bc
  conj : ∀ᶠ u in 𝓝 (0 : E 0), u ∈ U → (Ψ (u, k u)).2 = h (IsStrongBundleMap.base Ψ u)

attribute [instance] ConjugationData.i1 ConjugationData.i2 ConjugationData.i3 ConjugationData.i4
  ConjugationData.i5 ConjugationData.i6

/-- `IsConjugateToBasicGerm U k` is the existence of conjugation data. -/
theorem isConjugateToBasicGerm_iff_nonempty {k : E 0 → F 0} :
    IsConjugateToBasicGerm U k ↔ Nonempty (ConjugationData U k) := by
  constructor
  · rintro ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh,
      hev⟩
    exact ⟨⟨Pn, Q, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh, hev⟩⟩
  · rintro ⟨d⟩
    exact ⟨d.Pn, d.Q, d.i1, d.i2, d.i3, d.i4, d.i5, d.i6, d.W, d.Ct, d.U', d.Ψ, d.Ψ', d.G, d.h,
      d.Bc, d.quadrant, d.relOpen, d.iso, d.base_zero, d.germ_subset, d.basic, d.conj⟩

/-- **The derivative of a map conjugated to a basic germ is Fredholm of index `n − N`**, with
`n = dim Pn`, `N = dim Q` the dimensions of the given conjugation data: if `k : U → F` is
sc-smooth with `k(0) = 0` and `(Ψ(u, k(u)))₂ = h(ψ(u))` near `0` for a basic germ
`h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ ℝⁿ`, and a strong bundle isomorphism `Ψ` covering `ψ`, then
`Γ(0)Dk(0) = Dh(0)Dψ(0)`, so `Dk(0) = Γ(0)⁻¹ Dh(0) Dψ(0)` is Fredholm (level `0`) of index
`ind Dh(0) = n − N` (Proposition 3.10 for the basic germ).  The proof is that of
`IsConjugateToBasicGerm.scDeriv_isFredholm_wholeChart` with the dimensions kept. -/
theorem ConjugationData.scDeriv_isFredholm_index_wholeChart (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) {k : E 0 → F 0} (hk : IsScSmooth U k) (hk0 : k 0 = 0)
    (d : ConjugationData U k) :
    IsFredholm (scDeriv U k 0) ∧
      fredholmIndex (scDeriv U k 0) = finrank ℝ d.Pn - finrank ℝ d.Q := by
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
  have hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u' := fun u' hu' => hΨ.base_base' hu'
  have hψ'0 : ψ' 0 = 0 := hΨ.base_zero' h0 hψ0
  have hψsm : IsScSmooth U ψ := hΨ.toFun.base_isScSmooth hU
  have hψ'sm : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψU' : MapsTo ψ U U' := fun u hu => hΨ.toFun.base_mem hu
  have hψ'U : MapsTo ψ' U' U := fun u hu => hΨ.invFun.base_mem hu
  set Dk := scDeriv U k 0 with hDk
  set Dψ := scDeriv U ψ 0 with hDψ
  set Dψ' := scDeriv U' ψ' 0 with hDψ'
  set Dh := scDerivGerm (F := ScBanach.paramProd Q W) G h 0 with hDh
  set Γ := hΨ.toFun.fiberCLM h0 with hΓ
  set Γ' := hΨ.invFun.fiberCLM h0U' with hΓ'
  -- (a) `Dh(0)` is Fredholm of index `n − N`
  obtain ⟨hDhF, hDhind⟩ := proposition_3_10_basic_level_zero hCt hh
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
  -- (c) `Dψ(0)` and `Γ(0)` are isomorphisms
  have hlevψ' : levelMap ψ' 1 (0 : (ScBanach.paramProd Pn W) 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hψ'0])
  have hψψ'D : ∀ x, Dψ' (Dψ x) = x := fun x => by
    have := scDeriv_comp_eq_self hU hU' hψsm.isSc1 hψ'sm.isSc1 hψU' hψψ' h01 x
    rwa [hlevψ] at this
  have hψ'ψD : ∀ x, Dψ (Dψ' x) = x := fun x => by
    have := scDeriv_comp_eq_self hU' hU hψ'sm.isSc1 hψsm.isSc1 hψ'U hψ'ψ h01' x
    rwa [hlevψ'] at this
  set e₁ : E 0 ≃L[ℝ] (ScBanach.paramProd Pn W) 0 :=
    ContinuousLinearEquiv.equivOfInverse Dψ Dψ' hψψ'D hψ'ψD with he₁
  have hΓΓ' : ∀ y, Γ (Γ' y) = y := fun y => by
    simp only [hΓ, hΓ']
    have h1 : Ψ' (0, y) = (ψ' 0, (Ψ' (0, y)).2) := hΨ.invFun.apply_eq h0U' y
    rw [hψ'0] at h1
    have h2 := congrArg Prod.snd (hΨ.right_inv (0, y) ⟨h0U', mem_univ _⟩)
    rw [h1] at h2
    exact h2
  have hΓ'Γ : ∀ y, Γ' (Γ y) = y := fun y => by
    simp only [hΓ, hΓ']
    have h1 : Ψ (0, y) = (ψ 0, (Ψ (0, y)).2) := hΨ.toFun.apply_eq h0 y
    rw [hψ0] at h1
    have h2 := congrArg Prod.snd (hΨ.left_inv (0, y) ⟨h0, mem_univ _⟩)
    rw [h1] at h2
    exact h2
  set e₂ : (ScBanach.paramProd Q W) 0 ≃L[ℝ] F 0 :=
    ContinuousLinearEquiv.equivOfInverse Γ' Γ hΓΓ' hΓ'Γ with he₂
  -- (d) `Dk(0) = Γ(0)⁻¹ Dh(0) Dψ(0)`
  have hDk_eq : Dk = (e₂ : (ScBanach.paramProd Q W) 0 →L[ℝ] F 0).comp
      (Dh.comp (e₁ : E 0 →L[ℝ] (ScBanach.paramProd Pn W) 0)) := by
    ext x
    have := congrArg (fun T : E 0 →L[ℝ] (ScBanach.paramProd Q W) 0 => Γ' (T x)) hkey
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [hΓ'Γ] at this
    exact this
  obtain ⟨hF, hind⟩ := isFredholm_equiv_comp_equiv hDhF e₁ e₂
  rw [← hDk_eq] at hF hind
  exact ⟨hF, by rw [hind, hDhind]⟩

/-- **The index `n − N` does not depend on the conjugation**: for two conjugations `d`, `d'` of
the same sc-smooth `k` with `k(0) = 0` to basic germs, `dim d.Pn − dim d.Q = dim d'.Pn − dim d'.Q`
(both are the index of `Dk(0)`; the text's "the Fredholm index is invariant under strong bundle
isomorphisms"). -/
theorem ConjugationData.index_eq_wholeChart (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    {k : E 0 → F 0} (hk : IsScSmooth U k) (hk0 : k 0 = 0) (d d' : ConjugationData U k) :
    (finrank ℝ d.Pn : ℤ) - finrank ℝ d.Q = (finrank ℝ d'.Pn : ℤ) - finrank ℝ d'.Q := by
  rw [← (d.scDeriv_isFredholm_index_wholeChart hU h0 hk hk0).2, (d'.scDeriv_isFredholm_index_wholeChart hU h0 hk hk0).2]

end Conjugate

/-! ### Proposition 3.52 with the index of the conjugation -/

section Prop352

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **Proposition 3.52 in the chart of Definition 3.11, with the index**: let `g` be a filled
version of the principal part `f̂` of a section at a zero (`f̂(0) = 0`), `s` a local sc⁺-section
with `s(0) = g(0)` and `d` conjugation data of `g − s` to a basic germ
`h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W` with `C̃ ⊆ ℝⁿ`, `n = dim d.Pn`, `N = dim d.Q`.  Then `Dg(0) : E → F` is
a Fredholm operator (on level `0`) of index `n − N`, and so is `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀`
(Propositions 3.10, 1.10 and 3.5).  (`proposition_3_52_local_wholeChart` states the index as `n − N` for
some natural numbers.) -/
theorem proposition_3_52_local_index_wholeChart (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFilledVersion hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {s : E 0 → F 1}
    (hs : IsScSmooth (F := F.shift) U s) (hs0 : F.toBase 1 (s 0) = g 0)
    (d : ConjugationData U fun u => g u - F.toBase 1 (s u)) :
    ∃ (h1 : ∀ x, ρCLM hR h0 (scDeriv U g 0 (scDeriv U (r R) 0 x)) =
        scDeriv U g 0 (scDeriv U (r R) 0 x)),
      IsFredholm (scDeriv U g 0) ∧
      fredholmIndex (scDeriv U g 0) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
      IsFredholm (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1) ∧
      fredholmIndex (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1) =
        finrank ℝ d.Pn - finrank ℝ d.Q := by
  have hg : IsScSmooth U g := hfill.isScSmooth
  have hg0 : g 0 = 0 := by rw [← hfill.filler.eq_on.self_of_nhds h0O, hfb0]
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have huniq := hU.isScDomain.uniqueDiffWithinAt 1 0 h01
  -- `k = g − s` (written out: `d` depends on it)
  have hk : IsScSmooth U fun u => g u - F.toBase 1 (s u) :=
    hg.sub hU.isScDomain (hs.toBase_shift hU.isScDomain)
  have hk0 : (fun u => g u - F.toBase 1 (s u)) 0 = 0 := by
    change g 0 - F.toBase 1 (s 0) = 0
    rw [hs0, hg0, sub_self]
  obtain ⟨hDkF, hDkind⟩ := d.scDeriv_isFredholm_index_wholeChart hU h0 hk hk0
  -- `Dg(0) = Dk(0) + ιDs(0)`, with `ιDs(0)` compact
  have hDsop : IsScOperator (scDeriv (F := F.shift) U s 0) :=
    hs.isSc1.isSc1With_scDeriv.scOperator_deriv h01 (by
      change E.toBase 1 0 ∈ (E.smooth : Set (E 0))
      rw [map_zero]; exact E.smooth.zero_mem)
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
  have hcompact : IsCompactOperator (S.toScOperator 0) := S.isCompactOperator 0
  have hDgF : IsFredholm (scDeriv U g 0) := by
    rw [hDg]; exact isFredholm_add_isCompactOperator hDkF hcompact
  have hDgind : fredholmIndex (scDeriv U g 0) = finrank ℝ d.Pn - finrank ℝ d.Q := by
    rw [hDg, fredholmIndex_add_isCompactOperator hDkF hcompact, hDkind]
  -- Proposition 3.5
  obtain ⟨h1, -, hFiff, hindeq⟩ := hfill.filler.proposition_3_5 hg hg0 h0O hfK
  exact ⟨h1, hDgF, hDgind, hFiff.2 hDgF, by rw [hindeq, hDgind]⟩

end Prop352

/-! ### Proposition 3.52 for sections of strong bundles, with the index -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **Proposition 3.52, with the index**: let `f` be a section of the strong bundle `P : Y → X`
with `(f, x₀)` an sc-Fredholm germ and `f(x₀) = 0`.  In the strong bundle chart of Definition 3.11
centred at `x₀`, with the filled version `g` of the principal part `f̂` and the local sc⁺-section
`s` (`s(0) = g(0)`) for which `g − s` is conjugated to a basic germ, the linearizations `Dg(0)` and
`Tf(x₀) = Dg(0)|_{T₀O} : T₀O → K₀` (`fillerRestrict`) are Fredholm operators, and for **every**
conjugation `d` of `g − s` to a basic germ `h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ ℝⁿ`, their index
is `n − N = dim d.Pn − dim d.Q`.  (`proposition_3_52_wholeChart` states the index as `n − N` for some natural
numbers `n`, `N`, which every integer is; this is the statement with content.) -/
theorem proposition_3_52_index_wholeChart (hf : IsSection P f) {x₀ : X} (hg : B.IsScFredholmGermWholeChart f x₀)
    (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1)
      (_ : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g)
      (_ : IsScSmooth (F := c.F.shift) c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
      (_ : Nonempty (ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)))
      (h1 : ∀ x, ρCLM c.isRetraction h0 (scDeriv c.U g 0 (scDeriv c.U (r c.R) 0 x)) =
        scDeriv c.U g 0 (scDeriv c.U (r c.R) 0 x)),
      IsFredholm (scDeriv c.U g 0) ∧
      IsFredholm (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0)
        (scDeriv c.U g 0) h1) ∧
      ∀ d : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u)),
        fredholmIndex (scDeriv c.U g 0) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        fredholmIndex (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0)
          (scDeriv c.U g 0) h1) = finrank ℝ d.Pn - finrank ℝ d.Q := by
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
  have hne := isConjugateToBasicGerm_iff_nonempty.1 hconj
  obtain ⟨d₀⟩ := hne
  obtain ⟨h1, hDgF, -, hTF, -⟩ :=
    proposition_3_52_local_index_wholeChart c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hs hs0 d₀
  refine ⟨c, hc, hxV, hφ0, h0U, g, s, hfill, hs, hs0, ⟨d₀⟩, h1, hDgF, hTF, fun d => ?_⟩
  obtain ⟨h1', -, hDgind, -, hTind⟩ :=
    proposition_3_52_local_index_wholeChart c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hs hs0 d
  exact ⟨hDgind, hTind⟩

end Bundle

end Polyfold
