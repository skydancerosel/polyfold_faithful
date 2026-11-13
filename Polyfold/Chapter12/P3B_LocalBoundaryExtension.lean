import Polyfold.Chapter2.CornerGerms
import Polyfold.Chapter3.ParamPerturbation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §12.3, pp. 584–586:
**Definition 12.3.6** (local form), **Proposition 12.3.7** (2017: Proposition 12.2) and
**Corollary 12.3.8** (2017: Corollary 12.1): the local `∂`-extension of `sc⁺`-sections in a tame
local strong bundle model, with and without a finite group of symmetries.

# Local `∂`-extension of `sc⁺`-sections

## The text, paraphrased

(Definition 12.3.6) Over a tame ep-groupoid, a map `s : ∂X → W` with `P ∘ s = Id` is an
`sc⁺`-section over the boundary if its restriction to every local face `F ∋ x` (`x ∈ ∂X`) is an
`sc⁺`-section of `W|F → F`.
(Proposition 12.3.7) Let `K = R(U ◁ F) → O` be a tame local strong bundle model over the tame
retract `(O, C, E)`, and `s` an `sc⁺`-section defined on an open neighbourhood of `x₀` in `∂O`.
Then there is an `sc⁺`-section `s̃` on an open neighbourhood `V(x₀) ⊆ O` with `s̃ = s` on `∂O`
near `x₀`.  In coordinates `E = ℝⁿ ⊕ H`, `x₀ = (0, h₀)`, the proof sets `(t, h)_I = r(t_I, h)`
(`t_I` puts the coordinates in `I` to `0`) and
`s̃(t, h) = ∑_{j=1}^n (-1)^{j+1} ∑_{|I| = j} R((t, h), s((t, h)_I))`; an inclusion–exclusion
computation gives `s̃ = s` on `∂O`.
(Corollary 12.3.8) If moreover `G_{x₀}` acts on `O` by sc-diffeomorphisms with a lift to `K`, and
`s` is equivariant on a `G_{x₀}`-invariant neighbourhood of `x₀` in `∂O`, the average
`ŝ(x) = |G|⁻¹ ∑_g g⁻¹ ∗ s̃(g ∗ x)` is a `G_{x₀}`-invariant `sc⁺`-extension.

## What is formalized

* `Polyfold.retractBoundary E C O` (`∂O = O ∩ ∂C`) and the local form of Definition 12.3.6:
  `IsScPlusOnFaceNear T O K s x i` (near `x`, `s` restricted to the local face
  `O ∩ {t_i = 0}` is an `sc⁺`-section, and that face germ is an sc-retract) and
  `definition_12_3_6_local` (`IsBoundaryScPlusSectionOn`: this for all `x ∈ D` and all `i ∈ I(x)`).
* `Polyfold.boundaryExtension`: the text's formula, summed over the nonempty `I ⊆ I(x₀)`;
  `boundaryExtension_toBase_snd` shows it equals the text's `∑ (-1)^{|I|+1} R(z, s(z_I))`.
* `Polyfold.proposition_12_3_7` (the text's statement) and the stronger
  `proposition_12_3_7_of_faces_at` (the face condition is only used at `x₀`), both with the
  explicit extension `boundaryExtension`.
* `Polyfold.corollary_12_3_8`: the equivariant version, for a finite group acting on `O` with a
  linear lift to `K` (`LocalBundleAction`), by averaging.
* Nonvacuity: the zero section satisfies the hypothesis of Definition 12.3.6 in every tame local
  model (`isBoundaryScPlusSectionOn_zero`); the trivial action satisfies `LocalBundleAction`.

## Choices

* The tame local model is given with a presentation `T : E ≅ ℝⁿ ⊕ W` of `C`, and the local faces
  at `x` are the germs of `O ∩ {t_i = 0}`, `i ∈ I(x)` (Lemma 2.5.12, Corollary 2.5.13).  The text
  reduces to `x₀ = (0, h₀)` (all `n` coordinates vanish at `x₀`); here the sum runs over the
  nonempty `I ⊆ I(x₀)`, which is the same formula after that reduction.
* "`sc⁺`-section of `W|F → F`" for the face germ is `IsScPlusSection C (O ∩ V ∩ {t_i = 0}) K s`
  together with `IsScRetract E C (O ∩ V ∩ {t_i = 0})` (otherwise the quantifier over retractions in
  `IsScSmoothRetractMap` would be empty).
* `R((t,h), ·)` is read as `R` applied at the base point `(t, h)` to the fibre vector of
  `s((t,h)_I)`; by linearity of `R` in the fibre, the extension is written as one application of
  `R` to the alternating sum of the fibre vectors.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E F W : ScBanach} {n : ℕ}

/-! ### Coordinates of `P_σ` (the map `(t, h) ↦ (t_σ, h)`) -/

section Kill

variable (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))

lemma cornerInsertL_cornerRemoveL_apply (σ : Finset (Fin n)) (a : Fin n → ℝ) (l : Fin n) :
    cornerInsertL σ (cornerRemoveL σ a) l = if l ∈ σ then 0 else a l := by
  split_ifs with hl
  · exact cornerInsertL_apply_mem σ _ hl
  · obtain ⟨j, rfl⟩ := exists_cornerIdx σ hl
    rw [cornerInsertL_apply_idx, cornerRemoveL_apply]

lemma coord_cornerKill (σ : Finset (Fin n)) (y : E 0) (l : Fin n) :
    (T 0 (cornerKill T σ 0 y)).1 l = if l ∈ σ then 0 else (T 0 y).1 l := by
  rw [cornerKill_apply, cornerIncl_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact cornerInsertL_cornerRemoveL_apply σ _ l

lemma snd_cornerKill (σ : Finset (Fin n)) (y : E 0) :
    (T 0 (cornerKill T σ 0 y)).2 = (T 0 y).2 := by
  rw [cornerKill_apply, cornerIncl_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- `(t, h)_{I ∪ {i}} = (t, h)_I` when `t_i = 0`. -/
lemma cornerKill_insert_of_coord_eq_zero (σ : Finset (Fin n)) {i : Fin n} {y : E 0}
    (hy : (T 0 y).1 i = 0) : cornerKill T (insert i σ) 0 y = cornerKill T σ 0 y := by
  classical
  apply (T 0).injective
  refine Prod.ext (funext fun l => ?_) ?_
  · rw [coord_cornerKill, coord_cornerKill]
    by_cases hl : l = i
    · subst hl; simp [hy]
    · simp [Finset.mem_insert, hl]
  · rw [snd_cornerKill, snd_cornerKill]

lemma cornerKill_empty (y : E 0) : cornerKill T ∅ 0 y = y :=
  cornerKill_eq_self (T := T) ∅ (by simp)

end Kill

/-! ### Inclusion–exclusion -/

/-- The inclusion–exclusion identity of the proof of Proposition 12.3.7: if `v(I ∪ {i₀}) = v(I)`
for all `I ⊆ σ` with `i₀ ∈ σ`, then `∑_{∅ ≠ I ⊆ σ} (-1)^{|I|+1} v(I) = v(∅)`. -/
theorem sum_powerset_erase_empty_alternating {α M : Type*} [DecidableEq α] [AddCommGroup M]
    [Module ℝ M] (σ : Finset α) (v : Finset α → M) {i₀ : α} (hi₀ : i₀ ∈ σ)
    (hv : ∀ I ⊆ σ.erase i₀, v (insert i₀ I) = v I) :
    ∑ I ∈ σ.powerset.erase ∅, ((-1 : ℝ) ^ (I.card + 1)) • v I = v ∅ := by
  set f : Finset α → M := fun I => ((-1 : ℝ) ^ I.card) • v I with hf
  have htot : ∑ I ∈ σ.powerset, f I = 0 := by
    have hσ : σ = insert i₀ (σ.erase i₀) := (Finset.insert_erase hi₀).symm
    rw [hσ, Finset.sum_powerset_insert (Finset.notMem_erase i₀ σ), ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun I hI => ?_
    have hI' : I ⊆ σ.erase i₀ := Finset.mem_powerset.1 hI
    have hnot : i₀ ∉ I := fun h => Finset.notMem_erase i₀ σ (hI' h)
    simp only [hf, Finset.card_insert_of_notMem hnot, hv I hI', pow_succ, mul_neg, mul_one,
      neg_smul, add_neg_cancel]
  have hemp : (∅ : Finset α) ∈ σ.powerset := Finset.empty_mem_powerset σ
  have hsplit := Finset.add_sum_erase σ.powerset f hemp
  rw [htot] at hsplit
  have hneg : ∑ I ∈ σ.powerset.erase ∅, ((-1 : ℝ) ^ (I.card + 1)) • v I =
      -∑ I ∈ σ.powerset.erase ∅, f I := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [hf, pow_succ, mul_neg, mul_one, neg_smul]
  rw [hneg]
  have : f ∅ = v ∅ := by simp [hf]
  rw [← this]
  exact (neg_eq_of_add_eq_zero_left hsplit)

/-! ### The boundary `∂O` and Definition 12.3.6 in a tame local model -/

section LocalModel

/-- `∂O = O ∩ ∂C`: the points of `O` with `d_C ≠ 0` (for a tame retract `d_O = d_C` on `O`,
Proposition 2.5.6). -/
def retractBoundary (E : ScBanach) (C O : Set (E 0)) : Set (E 0) :=
  {z | z ∈ O ∧ degIndex E C z ≠ 0}

/-- **Definition 12.3.6** (one face germ): near `x`, the restriction of `s` to the local face
`O ∩ {t_i = 0}` is an `sc⁺`-section (and that face germ is an sc-retract). -/
def IsScPlusOnFaceNear (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (C O : Set (E 0))
    (K : Set (E 0 × F 0)) (s : E 0 → E 0 × F 1) (x : E 0) (i : Fin n) : Prop :=
  ∃ V : Set (E 0), IsOpen V ∧ x ∈ V ∧ IsScRetract E C (O ∩ V ∩ coordHyper T i) ∧
    IsScPlusSection C (O ∩ V ∩ coordHyper T i) K s

/-- **Definition 12.3.6** (2017: Definition 12.8), local form (and Definition 5.4.1 in a chart):
`s` is an **`sc⁺`-section over the boundary** on `D ⊆ ∂O` if for every `x ∈ D` and every local face
`O ∩ {t_i = 0}` at `x` (`i ∈ I(x)`), the restriction of `s` to that face is an `sc⁺`-section near
`x`. -/
def IsBoundaryScPlusSectionOn (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (C O : Set (E 0)) (K : Set (E 0 × F 0)) (s : E 0 → E 0 × F 1) (D : Set (E 0)) : Prop :=
  ∀ x ∈ D, ∀ i ∈ zeroSet T x, IsScPlusOnFaceNear T C O K s x i

variable (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))

lemma mem_retractBoundary_iff {C : Set (E 0)} (hT : C = T 0 ⁻¹' quadrant n W 0) {O : Set (E 0)}
    (hOC : O ⊆ C) {z : E 0} : z ∈ retractBoundary E C O ↔ z ∈ O ∧ (zeroSet T z).Nonempty := by
  constructor
  · rintro ⟨hz, hd⟩
    refine ⟨hz, Finset.card_ne_zero.1 ?_⟩
    rw [← degIndexWith_eq_card_zeroSet, ← degIndex_eq T hT (hOC hz)]; exact hd
  · rintro ⟨hz, hne⟩
    refine ⟨hz, ?_⟩
    rw [degIndex_eq T hT (hOC hz), degIndexWith_eq_card_zeroSet]
    exact Finset.card_ne_zero.2 hne

/-- **The extension of the proof of Proposition 12.3.7**:
`s̃(z) = R(z, ∑_{∅ ≠ I ⊆ σ} (-1)^{|I|+1} s(r(z_I)))` on `(U ◁ F)[1]`, where `z_I` puts the
coordinates in `I` to `0` (`cornerKill`) and `r` is the base retraction of `R`.  By linearity of
`R` in the fibre this is the text's `∑ (-1)^{|I|+1} R(z, s(z_I))`
(`boundaryExtension_toBase_snd`). -/
def boundaryExtension (RB : E 0 × F 0 → E 0 × F 0) (σ : Finset (Fin n)) (s : E 0 → E 0 × F 1)
    (z : E 0) : E 0 × F 1 :=
  shiftFiber RB (z, ∑ I ∈ σ.powerset.erase ∅,
    ((-1 : ℝ) ^ (I.card + 1)) • (s (IsStrongBundleMap.base RB (cornerKill T I 0 z))).2)

variable {C U : Set (E 0)} {RB : E 0 × F 0 → E 0 × F 0}

/-- The text's form of the extension: `s̃(z) = ∑_{∅ ≠ I ⊆ σ} (-1)^{|I|+1} R(z, s(z_I))`. -/
theorem boundaryExtension_toBase_snd (hRB : IsStrongBundleRetraction U RB) {z : E 0} (hz : z ∈ U)
    (σ : Finset (Fin n)) (s : E 0 → E 0 × F 1) :
    F.toBase 1 (boundaryExtension T RB σ s z).2 = ∑ I ∈ σ.powerset.erase ∅,
      ((-1 : ℝ) ^ (I.card + 1)) •
        (RB (z, F.toBase 1 (s (IsStrongBundleMap.base RB (cornerKill T I 0 z))).2)).2 := by
  let L : F 0 →ₗ[ℝ] F 0 := IsLinearMap.mk' (fun h => (RB (z, h)).2) (hRB.fiber_linear z hz)
  have hL : ∀ h, (RB (z, h)).2 = L h := fun _ => rfl
  unfold boundaryExtension
  rw [hRB.toBase_shiftFiber_snd (p := (z, _)) hz]
  simp only [map_sum, map_smul, hL]

lemma boundaryExtension_fst (hU : IsRelOpenInQuadrant E C U) (hRB : IsStrongBundleRetraction U RB)
    {z : E 0} (hz : z ∈ (hRB.baseRetraction hU).retract) (σ : Finset (Fin n))
    (s : E 0 → E 0 × F 1) : (boundaryExtension T RB σ s z).1 = z := by
  have hzU : z ∈ U := (hRB.baseRetraction hU).retract_subset hz
  change (RB (z, _)).1 = z
  rw [hRB.apply_fst hzU]
  exact (hRB.baseRetraction hU).apply_eq_self_of_mem_retract hz

lemma boundaryExtension_mem (hU : IsRelOpenInQuadrant E C U) (hRB : IsStrongBundleRetraction U RB)
    {z : E 0} (hz : z ∈ U) (σ : Finset (Fin n)) (s : E 0 → E 0 × F 1) :
    boundaryExtension T RB σ s z ∈ strongShiftOne (RB '' (U ×ˢ univ)) := by
  rw [← hRB.toScRetractionOne_retract hU]
  exact (hRB.toScRetractionOne hU).apply_mem_retract
    (show ((z, _) : (E.prod F.shift) 0) ∈ U ×ˢ univ from ⟨hz, mem_univ _⟩)

end LocalModel

/-! ### Proposition 12.3.7 -/

/-- Multiplication by a constant `c` as an sc-operator `F → F`. -/
def ScBanach.p3bSmulOp (F : ScBanach) (c : ℝ) : ScOperator F F where
  lvl m := c • ContinuousLinearMap.id ℝ (F m)
  incl_comm m x := by
    change F.incl m (c • x) = c • F.incl m x
    exact map_smul _ _ _

/-- `x ↦ c • g(x)` is sc-smooth for sc-smooth `g` and a constant `c`. -/
theorem IsScSmooth.p3bConstSmul {G : ScBanach} {U : Set (G 0)} (hU : IsScDomain G U)
    {g : G 0 → F 0} (hg : IsScSmooth U g) (c : ℝ) : IsScSmooth U fun x => c • g x := by
  have := IsScSmooth.comp hU (isScDomain_univ _)
    ((F.p3bSmulOp c).isScSmooth (isScDomain_univ _)) hg (mapsTo_univ _ _)
  exact this.congr hU fun _ _ => rfl

section Main

variable (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
variable {C U : Set (E 0)} {RB : E 0 × F 0 → E 0 × F 0}

/-- One term of the extension: for `∅ ≠ I ⊆ I(x₀)` and `i ∈ I`, if `s` is `sc⁺` on the face
`O ∩ {t_i = 0}` near `x₀`, then `z ↦ s(r(z_I))` is sc-smooth into `F¹` on `N ∩ C` for an open
`N ∋ x₀` (`r ∘ P_I` is the retraction onto the corner `O ∩ f_I` near `x₀`, `corner_retraction`). -/
theorem exists_isScSmooth_faceTerm (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hU : IsRelOpenInQuadrant E C U) (hRB : IsStrongBundleRetraction U RB)
    (htame : (hRB.baseRetraction hU).IsTameWith T) {x₀ : E 0}
    (hx₀ : x₀ ∈ (hRB.baseRetraction hU).retract) {s : E 0 → E 0 × F 1}
    {I : Finset (Fin n)} (hI : I ⊆ zeroSet T x₀) {i : Fin n} (hiI : i ∈ I)
    (hs : IsScPlusOnFaceNear T C (hRB.baseRetraction hU).retract (RB '' (U ×ˢ univ)) s x₀ i) :
    ∃ N : Set (E 0), IsOpen N ∧ x₀ ∈ N ∧
      IsScSmooth (F := F.shift) (N ∩ C)
        fun z => (s (IsStrongBundleMap.base RB (cornerKill T I 0 z))).2 := by
  set r := hRB.baseRetraction hU with hr
  obtain ⟨Vi, hVi, hx₀Vi, ⟨ρ, hρ⟩, hsQ⟩ := hs
  have hσ : ∀ l ∈ I, (T 0 x₀).1 l = 0 := fun l hl => (mem_zeroSet T).1 (hI hl)
  obtain ⟨-, -, -, VI, -, hx₀VI, S, -, hSeq, hSret, -⟩ := corner_retraction I hT htame hx₀ hσ
  set S' := S.restrict hVi with hS'
  obtain ⟨N, hN, hD⟩ := S'.relOpen.relOpen
  have hx₀S : x₀ ∈ S.retract := by rw [hSret]; exact ⟨⟨hx₀, hx₀VI⟩, hσ⟩
  have hx₀D : x₀ ∈ S'.U := ⟨S.retract_subset hx₀S, by
    change S x₀ ∈ Vi
    rw [S.apply_eq_self_of_mem_retract hx₀S]; exact hx₀Vi⟩
  have hx₀N : x₀ ∈ N := by rw [hD] at hx₀D; exact hx₀D.1
  refine ⟨N, hN, hx₀N, ?_⟩
  rw [← hD]
  have hSQ : ∀ z ∈ S'.U, S z ∈ ρ.retract := fun z hz => by
    rw [hρ]
    have h1 : S z ∈ S.retract := S.apply_mem_retract hz.1
    rw [hSret] at h1
    exact ⟨⟨h1.1.1, hz.2⟩, h1.2 i hiI⟩
  have hsm : IsScSmooth (F := E.prod F.shift) ρ.U (s ∘ ρ) := hsQ.isScSmooth.comp_isScSmooth ρ hρ
  have hcomp := IsScSmooth.comp S'.isScDomain ρ.isScDomain hsm S'.isScSmooth
    (fun z hz => ρ.retract_subset (hSQ z hz))
  refine (hcomp.snd S'.isScDomain).congr S'.isScDomain fun z hz => ?_
  change (s (ρ (S z))).2 = _
  rw [ρ.apply_eq_self_of_mem_retract (hSQ z hz), hSeq hz.1]
  rfl

/-- **Proposition 12.3.7** (2017: Proposition 12.2), stronger form: the face condition of
Definition 12.3.6 is only needed at `x₀` (for the `d(x₀)` local faces at `x₀`).  Then
`s̃ = boundaryExtension T R I(x₀) s` is an `sc⁺`-section on `O ∩ V` for an open `V ∋ x₀`, and
`s̃ = s` on `∂O ∩ V`. -/
theorem proposition_12_3_7_of_faces_at (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hU : IsRelOpenInQuadrant E C U) (hRB : IsStrongBundleRetraction U RB)
    (htame : (hRB.baseRetraction hU).IsTameWith T) {x₀ : E 0}
    (hx₀ : x₀ ∈ (hRB.baseRetraction hU).retract) {s : E 0 → E 0 × F 1}
    (hs : ∀ i ∈ zeroSet T x₀,
      IsScPlusOnFaceNear T C (hRB.baseRetraction hU).retract (RB '' (U ×ˢ univ)) s x₀ i) :
    ∃ V : Set (E 0), IsOpen V ∧ x₀ ∈ V ∧
      IsScRetract E C ((hRB.baseRetraction hU).retract ∩ V) ∧
      IsScPlusSection C ((hRB.baseRetraction hU).retract ∩ V) (RB '' (U ×ˢ univ))
        (boundaryExtension T RB (zeroSet T x₀) s) ∧
      ∀ z ∈ retractBoundary E C (hRB.baseRetraction hU).retract ∩ V,
        boundaryExtension T RB (zeroSet T x₀) s z = s z := by
  classical
  set r := hRB.baseRetraction hU with hr
  set σ := zeroSet T x₀ with hσdef
  set K := RB '' (U ×ˢ univ) with hK
  -- the face terms
  have hterm : ∀ I : Finset (Fin n), ∃ N : Set (E 0), IsOpen N ∧ x₀ ∈ N ∧
      (I ∈ σ.powerset.erase ∅ → IsScSmooth (F := F.shift) (N ∩ C)
        fun z => (s (IsStrongBundleMap.base RB (cornerKill T I 0 z))).2) := by
    intro I
    by_cases hI : I ∈ σ.powerset.erase ∅
    · obtain ⟨hne, hIσ⟩ := Finset.mem_erase.1 hI
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
      obtain ⟨N, hN, hx, hsm⟩ := exists_isScSmooth_faceTerm T hT hU hRB htame hx₀
        (Finset.mem_powerset.1 hIσ) hi (hs i (Finset.mem_powerset.1 hIσ hi))
      exact ⟨N, hN, hx, fun _ => hsm⟩
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h => absurd h hI⟩
  choose N hNo hxN hNsm using hterm
  -- the face neighbourhoods
  have hface : ∀ i : Fin n, ∃ V : Set (E 0), IsOpen V ∧ x₀ ∈ V ∧
      (i ∈ σ → IsScPlusSection C (r.retract ∩ V ∩ coordHyper T i) K s) := by
    intro i
    by_cases hi : i ∈ σ
    · obtain ⟨V, hV, hxV, -, hsV⟩ := hs i hi
      exact ⟨V, hV, hxV, fun _ => hsV⟩
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h => absurd h hi⟩
  choose Vf hVfo hxVf hVfs using hface
  -- zero sets near `x₀`
  obtain ⟨Z, hZsub, hZo, hxZ⟩ := mem_nhds_iff.1 (eventually_zeroSet_subset T x₀)
  set V := Z ∩ (⋂ I ∈ σ.powerset.erase ∅, N I) ∩ ⋂ i ∈ σ, Vf i with hVdef
  have hVo : IsOpen V := (hZo.inter (isOpen_biInter_finset fun I _ => hNo I)).inter
    (isOpen_biInter_finset fun i _ => hVfo i)
  have hxV : x₀ ∈ V := ⟨⟨hxZ, mem_iInter₂.2 fun I _ => hxN I⟩, mem_iInter₂.2 fun i _ => hxVf i⟩
  set ρ := r.restrict hVo with hρdef
  have hρ : ρ.retract = r.retract ∩ V := r.restrict_retract hVo
  refine ⟨V, hVo, hxV, ⟨ρ, hρ⟩, ⟨fun z hz => boundaryExtension_fst T hU hRB hz.1 σ s, ?_⟩, ?_⟩
  · -- sc-smoothness, checked with the retraction `ρ` onto `O ∩ V`
    rw [isScSmoothRetractMap_iff_exists ⟨ρ, hρ⟩]
    refine ⟨fun z hz => boundaryExtension_mem T hU hRB (r.retract_subset hz.1) σ s, ρ, hρ, ?_⟩
    have hD := ρ.isScDomain
    have hρO : ∀ y ∈ ρ.U, ρ y ∈ r.retract ∩ V := fun y hy => hρ ▸ ρ.apply_mem_retract hy
    have hsum : IsScSmooth (F := F.shift) ρ.U fun y => ∑ I ∈ σ.powerset.erase ∅,
        ((-1 : ℝ) ^ (I.card + 1)) • (s (IsStrongBundleMap.base RB (cornerKill T I 0 (ρ y)))).2 := by
      refine IsScSmooth.finsetSum hD _ fun I hI => ?_
      have hNdom : IsScDomain E (N I ∩ C) :=
        (show IsRelOpenInQuadrant E C (N I ∩ C) from
          ⟨r.relOpen.isPartialQuadrant, N I, hNo I, rfl⟩).isScDomain
      have hmaps : MapsTo ρ ρ.U (N I ∩ C) := fun y hy =>
        ⟨mem_iInter₂.1 (hρO y hy).2.1.2 I hI, r.retract_subset_C (hρO y hy).1⟩
      exact (IsScSmooth.comp hD hNdom (hNsm I hI) ρ.isScSmooth hmaps).p3bConstSmul hD _
    have hpair := ρ.isScSmooth.scPair hD hsum
    have hfull := IsScSmooth.comp hD (hU.prod_univ F.shift).isScDomain hRB.isScSmooth_one hpair
      fun y hy => ⟨r.retract_subset (hρO y hy).1, mem_univ _⟩
    exact hfull.congr hD fun y _ => rfl
  · -- `s̃ = s` on `∂O ∩ V`: inclusion–exclusion
    rintro z ⟨hzb, hzV⟩
    obtain ⟨hzO, ⟨i₀, hi₀⟩⟩ := (mem_retractBoundary_iff T hT r.retract_subset_C).1 hzb
    have hi₀σ : i₀ ∈ σ := hZsub hzV.1.1 hi₀
    have hi₀z : (T 0 z).1 i₀ = 0 := (mem_zeroSet T).1 hi₀
    have hzQ : z ∈ r.retract ∩ Vf i₀ ∩ coordHyper T i₀ :=
      ⟨⟨hzO, mem_iInter₂.1 hzV.2 i₀ hi₀σ⟩, hi₀z⟩
    have hsz := hVfs i₀ hi₀σ
    have hfst : (s z).1 = z := hsz.fst_eq z hzQ
    have hmem : s z ∈ strongShiftOne K := hsz.isScSmooth.mapsTo hzQ
    have hsum : ∑ I ∈ σ.powerset.erase ∅,
        ((-1 : ℝ) ^ (I.card + 1)) • (s (IsStrongBundleMap.base RB (cornerKill T I 0 z))).2 =
          (s z).2 := by
      rw [sum_powerset_erase_empty_alternating σ
        (fun I => (s (IsStrongBundleMap.base RB (cornerKill T I 0 z))).2) hi₀σ
        (fun I _ => by simp only [cornerKill_insert_of_coord_eq_zero T I hi₀z])]
      simp only [cornerKill_empty]
      change (s (r z)).2 = (s z).2
      rw [r.apply_eq_self_of_mem_retract hzO]
    unfold boundaryExtension
    rw [hsum]
    have hsz' : ((z, (s z).2) : (E.prod F.shift) 0) = s z := Prod.ext hfst.symm rfl
    rw [hsz']
    rw [← hRB.toScRetractionOne_retract hU] at hmem
    exact (hRB.toScRetractionOne hU).apply_eq_self_of_mem_retract hmem

/-- **Proposition 12.3.7** (2017: Proposition 12.2), as stated in the text: let `K = R(U ◁ F) → O`
be a tame local strong bundle model and `s` an `sc⁺`-section over the boundary (Definition 12.3.6)
on an open neighbourhood `∂O ∩ V₀` of `x₀` in `∂O`.  Then there are an open `V ∋ x₀` and an
`sc⁺`-section `s̃` of `K` over `O ∩ V` with `s̃ = s` on `∂O ∩ V`. -/
theorem proposition_12_3_7 (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hU : IsRelOpenInQuadrant E C U) (hRB : IsStrongBundleRetraction U RB)
    (htame : (hRB.baseRetraction hU).IsTameWith T) {x₀ : E 0} {V₀ : Set (E 0)}
    (_hV₀ : IsOpen V₀) (hx₀ : x₀ ∈ retractBoundary E C (hRB.baseRetraction hU).retract ∩ V₀)
    {s : E 0 → E 0 × F 1}
    (hs : IsBoundaryScPlusSectionOn T C (hRB.baseRetraction hU).retract (RB '' (U ×ˢ univ)) s
      (retractBoundary E C (hRB.baseRetraction hU).retract ∩ V₀)) :
    ∃ V : Set (E 0), IsOpen V ∧ x₀ ∈ V ∧ ∃ s' : E 0 → E 0 × F 1,
      IsScRetract E C ((hRB.baseRetraction hU).retract ∩ V) ∧
      IsScPlusSection C ((hRB.baseRetraction hU).retract ∩ V) (RB '' (U ×ˢ univ)) s' ∧
      ∀ z ∈ retractBoundary E C (hRB.baseRetraction hU).retract ∩ V, s' z = s z := by
  obtain ⟨V, hV, hxV, hret, hplus, heq⟩ :=
    proposition_12_3_7_of_faces_at T hT hU hRB htame hx₀.1.1 (hs x₀ hx₀)
  exact ⟨V, hV, hxV, _, hret, hplus, heq⟩

end Main

/-! ### Nonvacuity: the zero section, and a tame local model with boundary -/

section Witness

variable (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
variable {C U : Set (E 0)} {RB : E 0 × F 0 → E 0 × F 0}

/-- The zero section `z ↦ (z, 0)` is an `sc⁺`-section of `K` over every `Q ⊆ O`. -/
theorem isScPlusSection_zero_local (hU : IsRelOpenInQuadrant E C U)
    (hRB : IsStrongBundleRetraction U RB) {Q : Set (E 0)}
    (hQ : Q ⊆ (hRB.baseRetraction hU).retract) :
    IsScPlusSection C Q (RB '' (U ×ˢ univ)) (fun z => ((z, 0) : E 0 × F 1)) where
  fst_eq _ _ := rfl
  isScSmooth := by
    refine ⟨fun z hz => ?_, fun ρ _ => ?_⟩
    · change (z, F.toBase 1 0) ∈ RB '' (U ×ˢ univ)
      rw [map_zero, hRB.mem_image_iff hU]
      exact ⟨hQ hz,
        (hRB.fiber_linear z ((hRB.baseRetraction hU).retract_subset (hQ hz))).map_zero⟩
    · have := IsScSmooth.comp ρ.isScDomain (isScDomain_univ _)
        ((E.prodInlOp F.shift).isScSmooth (isScDomain_univ _)) ρ.isScSmooth (mapsTo_univ _ _)
      exact this.congr ρ.isScDomain fun _ _ => rfl

/-- **Nonvacuity of Definition 12.3.6**: in every tame local strong bundle model the zero section is
an `sc⁺`-section over the boundary on every `D ⊆ O` (the face germs are retracts by
`corner_retraction`). -/
theorem isBoundaryScPlusSectionOn_zero (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hU : IsRelOpenInQuadrant E C U) (hRB : IsStrongBundleRetraction U RB)
    (htame : (hRB.baseRetraction hU).IsTameWith T) {D : Set (E 0)}
    (hD : D ⊆ (hRB.baseRetraction hU).retract) :
    IsBoundaryScPlusSectionOn T C (hRB.baseRetraction hU).retract (RB '' (U ×ˢ univ))
      (fun z => ((z, 0) : E 0 × F 1)) D := by
  intro x hx i hi
  have hσ : ∀ j ∈ ({i} : Finset (Fin n)), (T 0 x).1 j = 0 := fun j hj => by
    rw [Finset.mem_singleton.1 hj]; exact (mem_zeroSet T).1 hi
  obtain ⟨-, -, -, V, hV, hxV, S, -, -, hSret, -⟩ := corner_retraction {i} hT htame (hD hx) hσ
  have hQ : S.retract = (hRB.baseRetraction hU).retract ∩ V ∩ coordHyper T i := by
    rw [hSret]; ext z; simp [coordHyper]
  exact ⟨V, hV, hxV, ⟨S, hQ⟩, isScPlusSection_zero_local hU hRB fun z hz => hz.1.1⟩

/-- The identity is a strong bundle retraction on `U ◁ F`. -/
theorem isStrongBundleRetraction_id_p3b (hU : IsRelOpenInQuadrant E C U) :
    IsStrongBundleRetraction (F := F) U _root_.id where
  mapsTo := mapsTo_id _
  fst_independent _ _ _ _ := rfl
  fiber_linear _ _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  preserves_filtration _ _ _ _ _ hu _ hh := ⟨hu, hh⟩
  isScSmooth_zero := isScSmooth_id (hU.prod_univ F).isScDomain
  isScSmooth_one := (isScSmooth_id (hU.prod_univ F.shift).isScDomain).congr
    (hU.prod_univ F.shift).isScDomain fun p _ => show p = shiftFiber _root_.id p from
      Prod.ext rfl (Function.leftInverse_invFun (F.toBase_injective 1) p.2).symm
  idem _ _ := rfl

/-- **The hypotheses of Proposition 12.3.7 are satisfiable**: on `C = [0,∞) ⊕ W` with the identity
strong bundle retraction (a tame local strong bundle model), `0 ∈ ∂O`, and the zero section is an
`sc⁺`-section over the whole boundary. -/
theorem proposition_12_3_7_nonvacuous (W F : ScBanach) :
    ∃ (C U : Set (((ScBanach.const (Fin 1 → ℝ)).prod W) 0))
      (RB : ((ScBanach.const (Fin 1 → ℝ)).prod W) 0 × F 0 →
        ((ScBanach.const (Fin 1 → ℝ)).prod W) 0 × F 0)
      (_hT : C = (ScIso.refl ((ScBanach.const (Fin 1 → ℝ)).prod W)) 0 ⁻¹' quadrant 1 W 0)
      (hU : IsRelOpenInQuadrant _ C U) (hRB : IsStrongBundleRetraction U RB),
      (hRB.baseRetraction hU).IsTameWith (ScIso.refl ((ScBanach.const (Fin 1 → ℝ)).prod W)) ∧
      (0 : ((ScBanach.const (Fin 1 → ℝ)).prod W) 0) ∈
        retractBoundary _ C (hRB.baseRetraction hU).retract ∧
      IsBoundaryScPlusSectionOn (ScIso.refl ((ScBanach.const (Fin 1 → ℝ)).prod W)) C
        (hRB.baseRetraction hU).retract (RB '' (U ×ˢ univ)) (fun z => ((z, 0) : _ × F 1))
        (retractBoundary _ C (hRB.baseRetraction hU).retract) := by
  set E₁ := (ScBanach.const (Fin 1 → ℝ)).prod W
  have hT : quadrant 1 W 0 = (ScIso.refl E₁) 0 ⁻¹' quadrant 1 W 0 := by ext; rfl
  have hU : IsRelOpenInQuadrant E₁ (quadrant 1 W 0) (quadrant 1 W 0) :=
    ⟨⟨1, W, ScIso.refl E₁, hT⟩, univ, isOpen_univ, (univ_inter _).symm⟩
  have hRB := isStrongBundleRetraction_id_p3b (F := F) hU
  have htame : (hRB.baseRetraction hU).IsTameWith (ScIso.refl E₁) :=
    ScRetraction.id_isTame hU 1 W _ hT
  have h0 : (0 : E₁ 0) ∈ (hRB.baseRetraction hU).retract :=
    ⟨0, fun _ => le_rfl, rfl⟩
  refine ⟨_, _, _, hT, hU, hRB, htame, ?_, ?_⟩
  · refine (mem_retractBoundary_iff (ScIso.refl E₁) hT
      (hRB.baseRetraction hU).retract_subset_C).2 ⟨h0, ⟨0, ?_⟩⟩
    rw [mem_zeroSet]; rfl
  · exact isBoundaryScPlusSectionOn_zero (ScIso.refl E₁) hT hU hRB htame fun z hz => hz.1

end Witness

/-! ### Corollary 12.3.8: the equivariant local extension -/

section Equivariant

variable {C U : Set (E 0)} {RB : E 0 × F 0 → E 0 × F 0}

/-- The fibres of `K[1]` over `O` are linear: `(x, ∑ cᵢ aᵢ) ∈ K[1]` if all `(x, aᵢ) ∈ K[1]`. -/
theorem mem_strongShiftOne_sum_smul (hU : IsRelOpenInQuadrant E C U)
    (hRB : IsStrongBundleRetraction U RB) {x : E 0} (hx : x ∈ (hRB.baseRetraction hU).retract)
    {ι : Type*} (S : Finset ι) (c : ι → ℝ) (a : ι → F 1)
    (ha : ∀ i ∈ S, ((x, a i) : (E.prod F.shift) 0) ∈ strongShiftOne (RB '' (U ×ˢ univ))) :
    ((x, ∑ i ∈ S, c i • a i) : (E.prod F.shift) 0) ∈ strongShiftOne (RB '' (U ×ˢ univ)) := by
  have hxU : x ∈ U := (hRB.baseRetraction hU).retract_subset hx
  let L : F 0 →ₗ[ℝ] F 0 := IsLinearMap.mk' (fun h => (RB (x, h)).2) (hRB.fiber_linear x hxU)
  have hL : ∀ h, (RB (x, h)).2 = L h := fun _ => rfl
  have hfix : ∀ i ∈ S, L (F.toBase 1 (a i)) = F.toBase 1 (a i) := fun i hi =>
    ((hRB.mem_image_iff hU).1 (ha i hi)).2
  change (x, F.toBase 1 (∑ i ∈ S, c i • a i)) ∈ RB '' (U ×ˢ univ)
  rw [hRB.mem_image_iff hU]
  refine ⟨hx, ?_⟩
  change (RB (x, F.toBase 1 (∑ i ∈ S, c i • a i))).2 = F.toBase 1 (∑ i ∈ S, c i • a i)
  rw [hL]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl fun i hi => by rw [hfix i hi]

/-- The data of Corollary 12.3.8: a group `G` acting on the retract `O` (`φ_g`, the text's `g ∗ x`)
by sc-smooth maps, with a lift `Ψ_g : K[1] → K[1]` covering `φ_g` and linear on the fibres; both are
group actions (so the `φ_g` are sc-diffeomorphisms of `O`, with inverses `φ_{g⁻¹}`). -/
structure LocalBundleAction (G : Type*) [Group G] (C O : Set (E 0)) (K : Set (E 0 × F 0)) where
  /-- The action `x ↦ g ∗ x` on the base. -/
  act : G → E 0 → E 0
  /-- The lifted action on `K[1]`. -/
  lift : G → (E.prod F.shift) 0 → (E.prod F.shift) 0
  act_smooth : ∀ g, IsScSmoothRetractMap E C O E C O (act g)
  act_one : ∀ x ∈ O, act 1 x = x
  act_mul : ∀ g h, ∀ x ∈ O, act (g * h) x = act g (act h x)
  lift_smooth : ∀ g, IsScSmoothRetractMap (E.prod F.shift) (C ×ˢ univ) (strongShiftOne K)
    (E.prod F.shift) (C ×ˢ univ) (strongShiftOne K) (lift g)
  lift_fst : ∀ g, ∀ p ∈ strongShiftOne K, (lift g p).1 = act g p.1
  lift_linear : ∀ g, ∀ x ∈ O, IsLinearMap ℝ fun a : F 1 => (lift g (x, a)).2
  lift_one : ∀ p ∈ strongShiftOne K, lift 1 p = p
  lift_mul : ∀ g h, ∀ p ∈ strongShiftOne K, lift (g * h) p = lift g (lift h p)

/-- **Nonvacuity of `LocalBundleAction`**: every group acts trivially. -/
def LocalBundleAction.trivial (G : Type*) [Group G] (C O : Set (E 0)) (K : Set (E 0 × F 0)) :
    LocalBundleAction G C O K where
  act _ := _root_.id
  lift _ := _root_.id
  act_smooth _ := isScSmoothRetractMap_id O
  act_one _ _ := rfl
  act_mul _ _ _ _ := rfl
  lift_smooth _ := isScSmoothRetractMap_id _
  lift_fst _ _ _ := rfl
  lift_linear _ _ _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  lift_one _ _ := rfl
  lift_mul _ _ _ _ := rfl

/-- The average `ŝ(x) = |G|⁻¹ ∑_g g⁻¹ ∗ s̃(g ∗ x)` of the proof of Corollary 12.3.8. -/
def LocalBundleAction.average {G : Type*} [Group G] [Fintype G] {O : Set (E 0)}
    {K : Set (E 0 × F 0)} (A : LocalBundleAction G C O K) (s' : E 0 → E 0 × F 1) (x : E 0) :
    E 0 × F 1 :=
  (x, (Fintype.card G : ℝ)⁻¹ • ∑ g : G, (A.lift g⁻¹ (s' (A.act g x))).2)

variable (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))

/-- **Corollary 12.3.8** (2017: Corollary 12.1): in a tame local strong bundle model, let a finite
group `G` (the isotropy group `G_{x₀}`, fixing `x₀`) act on `O` with a lift to `K`, and let `s` be
an `sc⁺`-section over the boundary on a `G`-invariant neighbourhood `∂O ∩ V₀` of `x₀` in `∂O`,
equivariant there (`s(g ∗ x) = g ∗ s(x)`).  Then on a `G`-invariant neighbourhood `O ∩ V` of `x₀`
there is a `G`-equivariant `sc⁺`-section `ŝ` with `ŝ = s` on `∂O ∩ V`; it is the average of the
extension of Proposition 12.3.7. -/
theorem corollary_12_3_8 {G : Type} [Group G] [Finite G] (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hU : IsRelOpenInQuadrant E C U) (hRB : IsStrongBundleRetraction U RB)
    (htame : (hRB.baseRetraction hU).IsTameWith T)
    (A : LocalBundleAction G C (hRB.baseRetraction hU).retract (RB '' (U ×ˢ univ)))
    {x₀ : E 0} {V₀ : Set (E 0)} (hV₀ : IsOpen V₀)
    (hx₀ : x₀ ∈ retractBoundary E C (hRB.baseRetraction hU).retract ∩ V₀)
    (hfix : ∀ g, A.act g x₀ = x₀)
    (hinv : ∀ g, MapsTo (A.act g) (retractBoundary E C (hRB.baseRetraction hU).retract ∩ V₀)
      (retractBoundary E C (hRB.baseRetraction hU).retract ∩ V₀))
    {s : E 0 → E 0 × F 1}
    (hs : IsBoundaryScPlusSectionOn T C (hRB.baseRetraction hU).retract (RB '' (U ×ˢ univ)) s
      (retractBoundary E C (hRB.baseRetraction hU).retract ∩ V₀))
    (hequiv : ∀ g, ∀ x ∈ retractBoundary E C (hRB.baseRetraction hU).retract ∩ V₀,
      s (A.act g x) = A.lift g (s x)) :
    ∃ V : Set (E 0), IsOpen V ∧ x₀ ∈ V ∧
      (∀ g, MapsTo (A.act g) ((hRB.baseRetraction hU).retract ∩ V)
        ((hRB.baseRetraction hU).retract ∩ V)) ∧
      ∃ ŝ : E 0 → E 0 × F 1, IsScRetract E C ((hRB.baseRetraction hU).retract ∩ V) ∧
        IsScPlusSection C ((hRB.baseRetraction hU).retract ∩ V) (RB '' (U ×ˢ univ)) ŝ ∧
        (∀ g, ∀ x ∈ (hRB.baseRetraction hU).retract ∩ V, ŝ (A.act g x) = A.lift g (ŝ x)) ∧
        ∀ z ∈ retractBoundary E C (hRB.baseRetraction hU).retract ∩ V, ŝ z = s z := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hK1 : IsScRetract (E.prod F.shift) (C ×ˢ univ) (strongShiftOne (RB '' (U ×ˢ univ))) :=
    ⟨hRB.toScRetractionOne hU, hRB.toScRetractionOne_retract hU⟩
  -- values of `s` on `∂O ∩ V₀`
  have hsval : ∀ z ∈ retractBoundary E C (hRB.baseRetraction hU).retract ∩ V₀,
      (s z).1 = z ∧ s z ∈ strongShiftOne (RB '' (U ×ˢ univ)) := by
    intro z hz
    obtain ⟨i, hi⟩ :=
      ((mem_retractBoundary_iff T hT (hRB.baseRetraction hU).retract_subset_C).1 hz.1).2
    obtain ⟨Vz, -, hzV, -, hplus⟩ := hs z hz i hi
    have hzQ : z ∈ (hRB.baseRetraction hU).retract ∩ Vz ∩ coordHyper T i :=
      ⟨⟨hz.1.1, hzV⟩, (mem_zeroSet T).1 hi⟩
    exact ⟨hplus.fst_eq z hzQ, hplus.isScSmooth.mapsTo hzQ⟩
  -- Proposition 12.3.7
  obtain ⟨V₁, hV₁, hxV₁, -, hplus, heq⟩ :=
    proposition_12_3_7_of_faces_at T hT hU hRB htame hx₀.1.1 (hs x₀ hx₀)
  set st := boundaryExtension T RB (zeroSet T x₀) s with hst
  -- the `G`-invariant neighbourhood
  have hcont : ∀ g, ContinuousOn (A.act g ∘ (hRB.baseRetraction hU))
      (hRB.baseRetraction hU).U := fun g =>
    ((A.act_smooth g).comp_isScSmooth (hRB.baseRetraction hU) rfl).isSc1.isSc0.continuousOn_base
  choose u hu huU using fun g => continuousOn_iff'.1 (hcont g) (V₁ ∩ V₀) (hV₁.inter hV₀)
  set V := ⋂ g, u g with hVdef
  have hVo : IsOpen V := isOpen_iInter_of_finite hu
  have hkey : ∀ x ∈ (hRB.baseRetraction hU).retract ∩ V, ∀ g, A.act g x ∈ V₁ ∩ V₀ :=
      fun x hx g => by
    have : x ∈ u g ∩ (hRB.baseRetraction hU).U :=
      ⟨mem_iInter.1 hx.2 g, (hRB.baseRetraction hU).retract_subset hx.1⟩
    rw [← huU g] at this
    have h1 := this.1
    simp only [mem_preimage, comp_apply,
      (hRB.baseRetraction hU).apply_eq_self_of_mem_retract hx.1] at h1
    exact h1
  have hxV : x₀ ∈ V := mem_iInter.2 fun g => by
    have : x₀ ∈ (A.act g ∘ (hRB.baseRetraction hU)) ⁻¹' (V₁ ∩ V₀) ∩
        (hRB.baseRetraction hU).U := by
      refine ⟨?_, (hRB.baseRetraction hU).retract_subset hx₀.1.1⟩
      simp only [mem_preimage, comp_apply,
        (hRB.baseRetraction hU).apply_eq_self_of_mem_retract hx₀.1.1, hfix g]
      exact ⟨hxV₁, hx₀.2⟩
    rw [huU g] at this; exact this.1
  have hinvV : ∀ k, MapsTo (A.act k) ((hRB.baseRetraction hU).retract ∩ V)
      ((hRB.baseRetraction hU).retract ∩ V) := fun k x hx => by
    have hkO : A.act k x ∈ (hRB.baseRetraction hU).retract := (A.act_smooth k).mapsTo hx.1
    refine ⟨hkO, mem_iInter.2 fun g => ?_⟩
    have : A.act k x ∈ (A.act g ∘ (hRB.baseRetraction hU)) ⁻¹' (V₁ ∩ V₀) ∩
        (hRB.baseRetraction hU).U := by
      refine ⟨?_, (hRB.baseRetraction hU).retract_subset hkO⟩
      simp only [mem_preimage, comp_apply,
        (hRB.baseRetraction hU).apply_eq_self_of_mem_retract hkO, ← A.act_mul g k x hx.1]
      exact hkey x hx (g * k)
    rw [huU g] at this; exact this.1
  -- the terms `x ↦ g⁻¹ ∗ s̃(g ∗ x)`
  have hterm : ∀ g, IsScSmoothRetractMap E C ((hRB.baseRetraction hU).retract ∩ V)
      (E.prod F.shift) (C ×ˢ univ) (strongShiftOne (RB '' (U ×ˢ univ)))
      (fun x => A.lift g⁻¹ (st (A.act g x))) := fun g => by
    have hφ : IsScSmoothRetractMap E C ((hRB.baseRetraction hU).retract ∩ V) E C
        ((hRB.baseRetraction hU).retract ∩ V₁) (A.act g) :=
      ((A.act_smooth g).restrict ⟨(hRB.baseRetraction hU), rfl⟩).mono_target fun x hx =>
        ⟨(A.act_smooth g).mapsTo hx.1, (hkey x hx g).1⟩
    have h1 := hplus.isScSmooth.comp hφ
      ⟨(hRB.baseRetraction hU).restrict hV₁, (hRB.baseRetraction hU).restrict_retract hV₁⟩
    exact (A.lift_smooth g⁻¹).comp h1 hK1
  have hterm_fst : ∀ g, ∀ x ∈ (hRB.baseRetraction hU).retract ∩ V,
      (A.lift g⁻¹ (st (A.act g x))).1 = x := by
    intro g x hx
    have hgx : A.act g x ∈ (hRB.baseRetraction hU).retract ∩ V₁ :=
      ⟨(A.act_smooth g).mapsTo hx.1, (hkey x hx g).1⟩
    rw [A.lift_fst _ _ (hplus.isScSmooth.mapsTo hgx), hplus.fst_eq _ hgx,
      ← A.act_mul _ _ _ hx.1, inv_mul_cancel, A.act_one x hx.1]
  have hterm_eq : ∀ g, ∀ x ∈ (hRB.baseRetraction hU).retract ∩ V,
      A.lift g⁻¹ (st (A.act g x)) = (x, (A.lift g⁻¹ (st (A.act g x))).2) := fun g x hx =>
    Prod.ext (hterm_fst g x hx) rfl
  have hmem : ∀ x ∈ (hRB.baseRetraction hU).retract ∩ V,
      A.average st x ∈ strongShiftOne (RB '' (U ×ˢ univ)) := by
    intro x hx
    unfold LocalBundleAction.average
    rw [Finset.smul_sum]
    refine mem_strongShiftOne_sum_smul hU hRB hx.1 _ (fun _ => _) _ fun g _ => ?_
    rw [← hterm_eq g x hx]
    exact (hterm g).mapsTo hx
  set ρ := (hRB.baseRetraction hU).restrict hVo with hρdef
  have hρ : ρ.retract = (hRB.baseRetraction hU).retract ∩ V :=
    (hRB.baseRetraction hU).restrict_retract hVo
  refine ⟨V, hVo, hxV, hinvV, A.average st, ⟨ρ, hρ⟩, ⟨fun x _ => rfl, ?_⟩, ?_, ?_⟩
  · -- `ŝ` is `sc⁺`
    rw [isScSmoothRetractMap_iff_exists ⟨ρ, hρ⟩]
    refine ⟨hmem, ρ, hρ, ?_⟩
    have hD := ρ.isScDomain
    have hsum : IsScSmooth (F := F.shift) ρ.U fun y =>
        (Fintype.card G : ℝ)⁻¹ • ∑ g : G, (A.lift g⁻¹ (st (A.act g (ρ y)))).2 := by
      refine IsScSmooth.p3bConstSmul hD (IsScSmooth.finsetSum hD _ fun g _ => ?_) _
      exact ((hterm g).comp_isScSmooth ρ hρ).snd hD
    exact (ρ.isScSmooth.scPair hD hsum).congr hD fun _ _ => rfl
  · -- equivariance
    intro k x hx
    have hkx := hinvV k hx
    have hmx := hmem x hx
    refine Prod.ext ?_ ?_
    · change A.act k x = (A.lift k (A.average st x)).1
      rw [A.lift_fst k _ hmx]; rfl
    · change (Fintype.card G : ℝ)⁻¹ • ∑ g : G, (A.lift g⁻¹ (st (A.act g (A.act k x)))).2 =
        (A.lift k (x, (Fintype.card G : ℝ)⁻¹ • ∑ g : G, (A.lift g⁻¹ (st (A.act g x))).2)).2
      let L : F 1 →ₗ[ℝ] F 1 := IsLinearMap.mk' _ (A.lift_linear k x hx.1)
      have hL : ∀ a, (A.lift k (x, a)).2 = L a := fun _ => rfl
      rw [hL, map_smul, map_sum]
      congr 1
      refine (Fintype.sum_equiv (Equiv.mulRight k) _ _ fun g => ?_)
      have hgk : A.act g (A.act k x) = A.act (g * k) x := (A.act_mul g k x hx.1).symm
      have hst_mem : st (A.act (g * k) x) ∈ strongShiftOne (RB '' (U ×ˢ univ)) :=
        hplus.isScSmooth.mapsTo ⟨(A.act_smooth _).mapsTo hx.1, (hkey x hx (g * k)).1⟩
      change (A.lift g⁻¹ (st (A.act g (A.act k x)))).2 =
        L (A.lift (g * k)⁻¹ (st (A.act (g * k) x))).2
      rw [← hL, ← hterm_eq (g * k) x hx, ← A.lift_mul _ _ _ hst_mem, hgk]
      congr 3
      group
  · -- `ŝ = s` on `∂O ∩ V`
    rintro z ⟨hzb, hzV⟩
    have hzV₀ : z ∈ V₀ := by
      have := (hkey z ⟨hzb.1, hzV⟩ 1).2
      rwa [A.act_one z hzb.1] at this
    obtain ⟨hfst, hzmem⟩ := hsval z ⟨hzb, hzV₀⟩
    have hterm_s : ∀ g : G, A.lift g⁻¹ (st (A.act g z)) = s z := fun g => by
      have hgz := hinv g ⟨hzb, hzV₀⟩
      rw [heq _ ⟨hgz.1, (hkey z ⟨hzb.1, hzV⟩ g).1⟩, hequiv g z ⟨hzb, hzV₀⟩,
        ← A.lift_mul _ _ _ hzmem, inv_mul_cancel, A.lift_one _ hzmem]
    unfold LocalBundleAction.average
    simp only [hterm_s, Finset.sum_const, Finset.card_univ]
    refine Prod.ext hfst.symm ?_
    change (Fintype.card G : ℝ)⁻¹ • (Fintype.card G • (s z).2) = (s z).2
    rw [← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]

end Equivariant

end Polyfold
