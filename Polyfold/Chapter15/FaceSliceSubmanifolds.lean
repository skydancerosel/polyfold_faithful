import Polyfold.Chapter15.CylinderEndStructures
import Polyfold.Chapter15.ProductEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definition 4.2.1 (p. 135),
Theorem 7.1.13 (p. 247) and the proof of Corollary 15.4.4 (p. 703).

# Submanifolds in a slice of a product, and product natural representations

## The text, paraphrased

In the proof of Corollary 15.4.4 the boundary of a sheet `M̃` of the cylinder `[0, 1] × X` near a
point `(i, x)` lies in the face `{i} × X` and is identified with a sheet of `X` near `x`; the
neighbourhood of `(i, x)` on which the isotropy group acts is a product `I × U(x)`.

## What is formalized

For sc-smooth maps `f : X → Y`, `g : Y → X` of M-polyfolds and a smooth finite-dimensional
submanifold `A ⊆ X` with `g ∘ f = id` on `A`:

* `MPolyfold.IsSmoothSubmanifold.image_of_leftInverseOn`: `f(A)` is a smooth finite-dimensional
  submanifold of `Y` (the sc⁺-retraction `f ∘ s ∘ g`).

For the slice inclusion `ι(x) = (q, x)` into a product `T × X` of M-polyfolds:

* `MPolyfold.IsSubmanifoldOfDim.of_image_prodMk`: a smooth submanifold `A` of `X` whose slice
  `{q} × A` has dimension `n` has dimension `n`.
* **`MPolyfold.IsSubmanifoldOfDim.slice`**: if `N ⊆ {q} × X` is an `n`-dimensional submanifold
  of `T × X`, then `{y | (q, y) ∈ N}` is an `n`-dimensional submanifold of `X`.

For the ep-groupoid `[0, 1]ⁿ × X`:

* **`EpGroupoid.NaturalRep.cubeProd`**: from a natural representation of `G_x` on `U(x)` and an
  open connected `I ∋ q`, the natural representation of `G_{(q, x)}` on `I × U(x)`, with
  `Φ(g)(t, y) = (t, Φ(g₂)(y))`.
* `SBLocalization.isConnected_cubeNhd`: the sets `{t | |t − i| < δ}` of `[0, 1]` are connected.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u v

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {f : X → Y} {g : Y → X}

/-- **The image of a smooth finite-dimensional submanifold `A` under an sc-smooth map `f` that
has an sc-smooth left inverse `g` on `A`** is a smooth finite-dimensional submanifold
(Definition 4.2.1): if `s` is an sc⁺-retraction onto `A ∩ W`, then `f ∘ s ∘ g` is one onto
`f(A) ∩ g⁻¹(W)`. -/
theorem IsSmoothSubmanifold.image_of_leftInverseOn (hf : P.IsScSmoothMap Q f)
    (hg : Q.IsScSmoothMap P g) {A : Set X} (hgf : ∀ a ∈ A, g (f a) = a)
    (hA : P.IsSmoothSubmanifold A) : Q.IsSmoothSubmanifold (f '' A) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨W, hW, haW, s, hs, himg⟩ := hA a ha
  have hsA : ∀ w ∈ W, s w ∈ A := fun w hw => by
    have h : s w ∈ s '' W := ⟨w, hw, rfl⟩
    rw [himg] at h
    exact h.1
  have hW'o : IsOpen (univ ∩ g ⁻¹' W) := hg.continuousOn.isOpen_inter_preimage isOpen_univ hW
  have hgW' : MapsTo g (univ ∩ g ⁻¹' W) W := fun y hy => hy.2
  have hmapsW' : MapsTo (f ∘ s ∘ g) (univ ∩ g ⁻¹' W) (univ ∩ g ⁻¹' W) := fun y hy =>
    ⟨mem_univ _, by
      change g (f (s (g y))) ∈ W
      rw [hgf _ (hsA _ hy.2)]; exact hs.mapsTo hy.2⟩
  obtain ⟨w₀, hw₀, hw₀a⟩ : a ∈ s '' W := himg ▸ ⟨ha, haW⟩
  have ha1 : a ∈ P.levelSet 1 := hw₀a ▸ hs.mem_levelSet w₀ hw₀
  have hg_sm : Q.IsScSmoothOn P g (univ ∩ g ⁻¹' W) := hg.mono hW'o (subset_univ _)
  have hfU : P.IsScSmoothOn Q f univ := hf
  refine ⟨univ ∩ g ⁻¹' W, hW'o, ⟨mem_univ _, by rw [mem_preimage, hgf a ha]; exact haW⟩,
    f ∘ s ∘ g, ⟨?_, hmapsW', fun y hy => ?_, fun y hy => ?_, fun y₀ => ?_⟩, ?_⟩
  · exact hfU.comp (hs.isScSmoothOn.comp hg_sm hgW') fun y _ => mem_univ _
  · simp only [Function.comp_apply]
    rw [hgf _ (hsA _ hy.2), hs.idem _ (hgW' hy)]
  · exact hfU.mapsTo_levelSet 1 ⟨mem_univ _, hs.mem_levelSet _ (hgW' hy)⟩
  · let x₀ : P.Level 1 := P.levelMk 1 a ha1
    let F₁ : P.Level 1 → Q.Level 1 := fun x => Q.toLevelOne y₀ (f (P.levelVal 1 x))
    have hF₁ : P.shift.IsScSmoothOn Q.shift F₁ {x | P.levelVal 1 x ∈ univ} :=
      hfU.levelOne fun x hx =>
        levelVal_toLevelOne y₀ (hfU.mapsTo_levelSet 1 ⟨hx, levelVal_mem x⟩)
    have hin : Q.IsScSmoothOn P.shift (P.toLevelOne x₀ ∘ s ∘ g) (univ ∩ g ⁻¹' W) :=
      (hs.isScSmoothOn_one x₀).comp hg_sm hgW'
    refine (hF₁.comp hin fun y _ => mem_univ _).congr fun y hy => ?_
    simp only [Function.comp_apply, F₁]
    rw [levelVal_toLevelOne x₀ (hs.mem_levelSet _ (hgW' hy))]
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨s (g y), hsA _ hy.2, rfl⟩, hmapsW' hy⟩
    · rintro ⟨⟨a', ha', rfl⟩, hz⟩
      have ha'W : a' ∈ W := by
        have h2 := hz.2
        rwa [mem_preimage, hgf a' ha'] at h2
      obtain ⟨w, hw, hwa⟩ : a' ∈ s '' W := himg ▸ ⟨ha', ha'W⟩
      refine ⟨f a', hz, ?_⟩
      simp only [Function.comp_apply]
      rw [hgf a' ha', ← hwa, hs.idem w hw]

section Slice

variable {T : Type v} [TopologicalSpace T] [T2Space T] [ParacompactSpace T] {P₀ : MPolyfold T}
  [ParacompactSpace (T × X)] {q : T}

variable (hι : P.IsScSmoothMap (P₀.prod P) fun x => (q, x))
include hι

/-- **The dimension of `A` is the dimension of the slice `{q} × A`.** -/
theorem IsSubmanifoldOfDim.of_image_prodMk {A : Set X} {n : ℕ} (hA : P.IsSmoothSubmanifold A)
    (h : (P₀.prod P).IsSubmanifoldOfDim ((fun x => (q, x)) '' A) n) :
    P.IsSubmanifoldOfDim A n := by
  refine ⟨hA, fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := hA.exists_hasDimAt ha
  have hn := h.2 (q, a) ⟨a, ha, rfl⟩
  obtain ⟨χ, hχ, hqχ⟩ := P₀.exists_isChart_mem_source q
  obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a
  obtain ⟨NA, hNA, -⟩ := exists_submodule_chartTangent hφ hA ha haφ
  obtain ⟨NB, hNB, -⟩ := exists_submodule_chartTangent (hχ.prod hφ) h.1 (y := (q, a))
    ⟨a, ha, rfl⟩ ⟨hqχ, haφ⟩
  have hra := finrank_chartTangent hφ hk hA haφ hNA
  have hrb := finrank_chartTangent (hχ.prod hφ) hn h.1 (y := (q, a)) ⟨hqχ, haφ⟩ hNB
  have hmap : NB = NA.map (LinearMap.inr ℝ (χ.model.E 0) (φ.model.E 0)) := by
    refine SetLike.coe_injective ?_
    rw [hNB, chartTangent_image_prodMk hι hχ hqχ hφ hA ha haφ, ← hNA]
    rfl
  have hfr : Module.finrank ℝ NB = Module.finrank ℝ NA := by
    rw [hmap]
    exact (Submodule.equivMapOfInjective _ LinearMap.inr_injective NA).finrank_eq.symm
  have hkn : k = n := by rw [← hra, ← hfr, hrb]
  exact hkn ▸ hk

/-- **A submanifold of the product that lies in the slice `{q} × X` is a submanifold of `X`**,
of the same dimension: the sc⁺-retraction `pr₂ ∘ s ∘ ι`. -/
theorem IsSubmanifoldOfDim.slice {N : Set (T × X)} {n : ℕ}
    (hN : (P₀.prod P).IsSubmanifoldOfDim N n) (hq : ∀ p ∈ N, p.1 = q) :
    P.IsSubmanifoldOfDim {y | (q, y) ∈ N} n := by
  have e1 : {y | (q, y) ∈ N} = Prod.snd '' N := by
    ext y
    constructor
    · intro hy; exact ⟨(q, y), hy, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      have : p = (q, p.2) := Prod.ext (hq p hp) rfl
      change (q, p.2) ∈ N
      rw [← this]; exact hp
  have e2 : (fun x => (q, x)) '' {y | (q, y) ∈ N} = N := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hp
      have : p = (q, p.2) := Prod.ext (hq p hp) rfl
      exact ⟨p.2, by change (q, p.2) ∈ N; rw [← this]; exact hp, this.symm⟩
  have hS : P.IsSmoothSubmanifold {y | (q, y) ∈ N} := by
    rw [e1]
    exact hN.1.image_of_leftInverseOn (isScSmoothMap_snd P₀ P) hι
      (fun p hp => Prod.ext (hq p hp).symm rfl)
  exact IsSubmanifoldOfDim.of_image_prodMk hι hS (by rw [e2]; exact hN)

end Slice

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} [ParacompactSpace ((Fin n → unitInterval) × Obj)]
  [ParacompactSpace ((Fin n → unitInterval) × Mor)]

/-- **The natural representation of `G_{(q, x)}` on `I × U(x)`** (Theorem 7.1.13 for
`[0, 1]ⁿ × X`): for a natural representation `(Φ, Γ)` of `G_x` on `U(x)` and an open connected
`I ∋ q`, `Φ̃(g)(t, y) = (t, Φ(g₂)(y))` and `Γ̃(g, (t, y)) = (t, Γ(g₂, y))`. -/
def NaturalRep.cubeProd {x : Obj} (R : X.NaturalRep x) {q : Fin n → unitInterval}
    {I : Set (Fin n → unitInterval)} (hI : IsOpen I) (hIc : IsConnected I) (hq : q ∈ I) :
    (X.cubeProd n).NaturalRep (q, x) where
  U := I ×ˢ R.U
  isOpen_U := hI.prod R.isOpen_U
  isConnected_U := hIc.prod R.isConnected_U
  mem_U := ⟨hq, R.mem_U⟩
  Φ g := Prod.map id (R.Φ (X.cubeIsotropyHom n (q, x) g))
  Γ g := Prod.map id (R.Γ (X.cubeIsotropyHom n (q, x) g))
  isScDiffeoOn_Φ g := by
    have hid : (cubePolyfold n).IsScDiffeoOn (cubePolyfold n) id id I I :=
      ⟨MPolyfold.isScSmoothMap_id.mono hI (subset_univ _),
        MPolyfold.isScSmoothMap_id.mono hI (subset_univ _), fun _ h => h, fun _ h => h,
        fun _ _ => rfl, fun _ _ => rfl⟩
    have h := MPolyfold.IsScDiffeoOn.prodMap hid
      (R.isScDiffeoOn_Φ (X.cubeIsotropyHom n (q, x) g))
    rw [← map_inv] at h
    exact h
  Φ_mul g h p hp := by
    refine Prod.ext rfl ?_
    change R.Φ (X.cubeIsotropyHom n (q, x) (g * h)) p.2 = _
    rw [map_mul]
    exact R.Φ_mul _ _ p.2 hp.2
  isScSmoothOn_Γ g :=
    MPolyfold.IsScSmoothOn.prodMap (MPolyfold.isScSmoothMap_id.mono hI (subset_univ _))
      (R.isScSmoothOn_Γ (X.cubeIsotropyHom n (q, x) g))
  Γ_self g := by
    have h1 : (g.val).1 = q := congrArg Prod.fst g.src_val
    refine Prod.ext h1.symm ?_
    change R.Γ (X.cubeIsotropyHom n (q, x) g) x = g.val.2
    rw [R.Γ_self]
    rfl
  src_Γ g p hp := Prod.ext rfl (R.src_Γ _ p.2 hp.2)
  tgt_Γ g p hp := Prod.ext rfl (R.tgt_Γ _ p.2 hp.2)
  existsUnique_Γ h hs ht := by
    obtain ⟨g₂, hg₂, huniq⟩ := R.existsUnique_Γ h.2 hs.2 ht.2
    obtain ⟨g, rfl⟩ := (X.bijective_cubeIsotropyHom n (q, x)).2 g₂
    refine ⟨g, Prod.ext rfl hg₂, fun g' hg' => ?_⟩
    exact (X.bijective_cubeIsotropyHom n (q, x)).1 (huniq _ (congrArg Prod.snd hg'))

@[simp] theorem NaturalRep.cubeProd_U {x : Obj} (R : X.NaturalRep x) {q : Fin n → unitInterval}
    {I : Set (Fin n → unitInterval)} (hI : IsOpen I) (hIc : IsConnected I) (hq : q ∈ I) :
    (R.cubeProd hI hIc hq).U = I ×ˢ R.U := rfl

end EpGroupoid

namespace SBLocalization

/-- **The interval neighbourhoods of `[0, 1]`**: `{t | |t − i| < δ}` is connected (the image of
an interval of `ℝ` under the projection onto `[0, 1]`). -/
theorem isConnected_cubeNhd (i : unitInterval) {δ : ℝ} (hδ : 0 < δ) :
    IsConnected {t : Fin 1 → unitInterval | |(t 0 : ℝ) - i| < δ} := by
  have hc : Continuous fun r : ℝ => (fun _ : Fin 1 => Set.projIcc (0 : ℝ) 1 zero_le_one r) :=
    continuous_pi fun _ => continuous_projIcc
  have himg : {t : Fin 1 → unitInterval | |(t 0 : ℝ) - i| < δ} =
      (fun r : ℝ => (fun _ : Fin 1 => Set.projIcc (0 : ℝ) 1 zero_le_one r)) ''
        Ioo ((i : ℝ) - δ) (i + δ) := by
    ext t
    constructor
    · intro ht
      have ht' := abs_lt.1 (show |(t 0 : ℝ) - i| < δ from ht)
      refine ⟨(t 0 : ℝ), ⟨by linarith [ht'.1], by linarith [ht'.2]⟩, funext fun a => ?_⟩
      rw [Subsingleton.elim a 0]
      exact Set.projIcc_of_mem zero_le_one (t 0).2
    · rintro ⟨r, hr, rfl⟩
      change |((Set.projIcc (0 : ℝ) 1 zero_le_one r : unitInterval) : ℝ) - i| < δ
      have h0 := i.2.1
      have h1 := i.2.2
      rw [Set.coe_projIcc, abs_lt]
      constructor
      · have : max 0 (min 1 r) ≥ min 1 r := le_max_right _ _
        rcases le_total 1 r with h | h
        · rw [min_eq_left h] at this ⊢; rw [max_eq_right zero_le_one]; linarith
        · rw [min_eq_right h] at this ⊢; linarith [hr.1]
      · have : max 0 (min 1 r) ≤ max 0 r := max_le_max le_rfl (min_le_right _ _)
        rcases le_total 0 r with h | h
        · rw [max_eq_right h] at this; linarith [hr.2]
        · rw [max_eq_left h] at this; linarith
  rw [himg]
  exact (isConnected_Ioo (by linarith)).image _ hc.continuousOn

end SBLocalization

end Polyfold
