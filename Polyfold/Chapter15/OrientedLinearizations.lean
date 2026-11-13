import Polyfold.Chapter6.SolutionSetOrientation
import Polyfold.Chapter6.SolutionOrientationCharts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702: the oriented formal sums `Ĝr_F(x)` before **Theorem 15.4.1** (2017: before
Theorem 15.6), read in a chart point of Part I.

# Oriented members of `Lin(f, x)` and their formal sums

## The text, paraphrased

(p. 701) For a smooth `x`, `Ĝr_F(x)` is the set of finite formal sums `∑ σ_L̂ · L̂` with
nonnegative rational weights of oriented sc-Fredholm operators `L̂ = (L, o)`, `o` an orientation
of `det(L)`.  Forgetting orientations is a 2-1 functor `f_F : Ĝr_F(X) → Gr_F(X)`.  If `f` is
oriented by `o`, every `(f − s)'(x)` with `s(x) = f(x)` inherits an orientation; for `L` onto it
is an orientation of `Λ^max ker L`, identified with `det L`.

## What is formalized (namespace `Polyfold.ChartPoint`)

The operators are read in a chart point `p` of Part I (`T_zO → K_z`), as Part I's `Lin(f, x)`.

* `OrLin p f`: the pairs `(L, r)` with `L ∈ Lin(f, x)` and `r` an orientation of `det L`;
  `GrFHat p f`, the formal sums with weights in `ℚ≥0`; `forgetOr` (the forgetful map `f_F`).
* `exists_two_orLin`: over every `L ∈ Lin(f, x)` there are exactly two oriented operators
  (the 2-1 property of `f_F`).
* `orLin o L = (L, o(L))` for an orientation `o ∈ Or_x^f`, and `canonLift o w`, the oriented
  sum of a formal sum `w` of members of `Lin(f, x)`; `forgetOr_canonLift` (`f_F ∘ lift = id`),
  `canonLift_unique` (a lift all of whose summands carry the orientation induced by `o` is
  `canonLift o w`), `canonLift_injective_o` (different `o` give different lifts of a nonzero
  sum).
* `orKer o hL hLs hN`: for `L ∈ Lin(f, x)` onto, the orientation `o(L)` read in `Λ^max N` with
  `N ⊆ E₀` the image of `ker L` (the text's identification `det L ≅ Λ^max ker L`);
  `orKerEquiv` (it is a bijection `Or_x^f ≃ Ray(Λ^max N)`), `orKerOrientation` (the
  orientation of `N` as a Mathlib `Orientation`, via `pullOr`).
-/

set_option maxSynthPendingDepth 3

open Set Module

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x)

variable (f) in
/-- **An oriented member of `Lin(f, x)`** (2021 p. 701): `L ∈ Lin(f, x)` with an orientation of
`det L` (the fibre of `DET(f, x)` over `L`). -/
def OrLin (hf : B.IsScFredholmSection f) : Type _ :=
  Σ L : p.linSet f, Module.Ray ℝ (p.detLin f hf L)

variable (f) in
/-- **`Ĝr_F(x)` in the chart point `p`** (2021 p. 701): finite formal sums of oriented members
of `Lin(f, x)` with weights in `ℚ≥0`. -/
abbrev GrFHat (hf : B.IsScFredholmSection f) : Type _ := p.OrLin f hf →₀ ℚ≥0

variable (f) in
/-- **The forgetful map `f_F`** (2021 p. 701): `∑ σ · (L, r) ↦ ∑ σ · L`. -/
def forgetOr (hf : B.IsScFredholmSection f) (w : p.GrFHat f hf) :
    (↥p.T →L[ℝ] ↥p.K) →₀ ℚ≥0 :=
  Finsupp.mapDomain (fun q : p.OrLin f hf => ((q.1 : p.linSet f) : ↥p.T →L[ℝ] ↥p.K)) w

/-- A real line has exactly two rays. -/
theorem exists_two_rays_of_finrank_eq_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    (h1 : finrank ℝ V = 1) : ∃ r₁ r₂ : Module.Ray ℝ V, r₁ ≠ r₂ ∧ ∀ r, r = r₁ ∨ r = r₂ := by
  have hpos : 0 < finrank ℝ V := by rw [h1]; exact one_pos
  have : Module.Finite ℝ V := Module.finite_of_finrank_pos hpos
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  exact ⟨_, _, Module.Ray.ne_neg_self _, fun r => ray_eq_or_eq_neg_of_finrank_eq_one h1 hv r⟩

/-- **`f_F` is 2-1**: over every `L ∈ Lin(f, x)` there are exactly two oriented operators. -/
theorem exists_two_orLin (hf : B.IsScFredholmSection f) (L : p.linSet f) :
    ∃ q₁ q₂ : p.OrLin f hf, q₁.1 = L ∧ q₂.1 = L ∧ q₁ ≠ q₂ ∧
      ∀ q : p.OrLin f hf, q.1 = L → q = q₁ ∨ q = q₂ := by
  obtain ⟨L, hL⟩ := L
  obtain ⟨r₁, r₂, hne, hr⟩ := exists_two_rays_of_finrank_eq_one
    (finrank_fredholmDet (p.isFredholm_of_mem_linSet hf L hL))
  refine ⟨⟨⟨L, hL⟩, r₁⟩, ⟨⟨L, hL⟩, r₂⟩, rfl, rfl,
    fun h => hne (eq_of_heq (Sigma.mk.inj_iff.1 h).2), ?_⟩
  rintro ⟨⟨L', hL'⟩, r⟩ hLL
  obtain rfl : L' = L := congrArg Subtype.val hLL
  rcases hr r with h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inr rfl

variable {hf : B.IsScFredholmSection f}

/-- **The oriented operator `(L, o(L))`** for an orientation `o ∈ Or_x^f` (2021 p. 701: every
member of `Lin(f, x)` inherits an orientation from `o`). -/
def orLin (o : p.Or f hf) (L : p.linSet f) : p.OrLin f hf := ⟨L, o L⟩

@[simp] theorem orLin_fst (o : p.Or f hf) (L : p.linSet f) : (p.orLin o L).1 = L := rfl

theorem orLin_injective (o : p.Or f hf) : Function.Injective (p.orLin o) := fun _ _ h =>
  congrArg Sigma.fst h

/-- **The canonical oriented lift** of a formal sum `w` of members of `Lin(f, x)`:
`∑ σ_L · L ↦ ∑ σ_L · (L, o(L))`. -/
def canonLift (o : p.Or f hf) (w : p.linSet f →₀ ℚ≥0) : p.GrFHat f hf :=
  Finsupp.mapDomain (p.orLin o) w

/-- **`f_F ∘ (canonical lift) = id`**. -/
theorem forgetOr_canonLift (o : p.Or f hf) (w : p.linSet f →₀ ℚ≥0) :
    p.forgetOr f hf (p.canonLift o w) = Finsupp.mapDomain Subtype.val w := by
  unfold forgetOr canonLift
  rw [← Finsupp.mapDomain_comp]
  rfl

theorem canonLift_single (o : p.Or f hf) (L : p.linSet f) (c : ℚ≥0) :
    p.canonLift o (Finsupp.single L c) = Finsupp.single (p.orLin o L) c :=
  Finsupp.mapDomain_single

theorem canonLift_add (o : p.Or f hf) (w w' : p.linSet f →₀ ℚ≥0) :
    p.canonLift o (w + w') = p.canonLift o w + p.canonLift o w' :=
  Finsupp.mapDomain_add

theorem canonLift_sum {ι : Type*} (o : p.Or f hf) (I : Finset ι) (w : ι → p.linSet f →₀ ℚ≥0) :
    p.canonLift o (∑ i ∈ I, w i) = ∑ i ∈ I, p.canonLift o (w i) :=
  Finsupp.mapDomain_finsetSum

/-- Every summand of `canonLift o w` carries the orientation induced by `o`. -/
theorem snd_eq_of_mem_support_canonLift (o : p.Or f hf) (w : p.linSet f →₀ ℚ≥0)
    {q : p.OrLin f hf} (hq : q ∈ (p.canonLift o w).support) : q = p.orLin o q.1 := by
  classical
  have h := Finsupp.mapDomain_support (f := p.orLin o) (s := w) hq
  rw [Finset.mem_image] at h
  obtain ⟨L, -, rfl⟩ := h
  rfl

/-- **Uniqueness of the canonical lift**: a formal sum of oriented operators whose summands all
carry the orientation induced by `o`, and whose image under `f_F` is `w`, is `canonLift o w`. -/
theorem canonLift_unique (o : p.Or f hf) (w : p.linSet f →₀ ℚ≥0) (W : p.GrFHat f hf)
    (hW : Finsupp.mapDomain Sigma.fst W = w) (hsupp : ∀ q ∈ W.support, q = p.orLin o q.1) :
    W = p.canonLift o w := by
  subst hW
  calc W = Finsupp.mapDomain id W := Finsupp.mapDomain_id.symm
    _ = Finsupp.mapDomain (p.orLin o ∘ Sigma.fst) W :=
        Finsupp.mapDomain_congr fun q hq => hsupp q hq
    _ = p.canonLift o (Finsupp.mapDomain Sigma.fst W) := Finsupp.mapDomain_comp

/-- `w ↦ ∑ σ_L · L` (as operators `T_zO → K_z`) is injective on formal sums of members of
`Lin(f, x)`. -/
theorem mapDomain_val_injective :
    Function.Injective (Finsupp.mapDomain (Subtype.val : p.linSet f → ↥p.T →L[ℝ] ↥p.K) :
      (p.linSet f →₀ ℚ≥0) → _) :=
  Finsupp.mapDomain_injective Subtype.val_injective

/-- **The canonical lift is determined by the underlying sum**: two formal sums of members of
`Lin(f, x)` with the same image in `Gr_F` have the same canonical lift. -/
theorem canonLift_eq_of_mapDomain_eq (o : p.Or f hf) {w w' : p.linSet f →₀ ℚ≥0}
    (h : Finsupp.mapDomain Subtype.val w = Finsupp.mapDomain Subtype.val w') :
    p.canonLift o w = p.canonLift o w' := by
  rw [p.mapDomain_val_injective h]

/-- **Different orientations give different lifts** of a nonzero sum. -/
theorem canonLift_injective_o {o o' : p.Or f hf} {w : p.linSet f →₀ ℚ≥0} (hw : w ≠ 0)
    (h : p.canonLift o w = p.canonLift o' w) : o = o' := by
  obtain ⟨L, hL⟩ := Finsupp.support_nonempty_iff.2 hw
  have hq : p.orLin o L ∈ (p.canonLift o w).support := by
    rw [canonLift, Finsupp.mem_support_iff,
      Finsupp.mapDomain_apply (p.orLin_injective o)]
    exact Finsupp.mem_support_iff.1 hL
  rw [h] at hq
  have h2 := p.snd_eq_of_mem_support_canonLift o' w hq
  have hr : o L = o' L := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
  have : PreconnectedSpace (p.linSet f) :=
    isPreconnected_iff_preconnectedSpace.1 (p.convex_linSet hf).isPreconnected
  exact LineOrientation.eq_of_apply_eq L hr

/-! ### The orientation of the kernel of an onto member -/

/-- **The orientation of `ker L` induced by `o`**, for `L ∈ Lin(f, x)` onto (2021 pp. 701–702:
`Λ^max ker L` is identified with `det L`): `o(L)` read in `Λ^max N` with `N ⊆ E₀` the image of
`ker L` (`surjRay`). -/
def orKer (o : p.Or f hf) {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f)
    (hLs : Function.Surjective L) {N : Submodule ℝ (p.c.φ.model.E 0)}
    (hN : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N) : Module.Ray ℝ (maxPow N) :=
  surjRay hLs p.T.subtypeL Subtype.val_injective hN (o ⟨L, hL⟩)

/-- **`o ↦ orKer o` is a bijection** `Or_x^f ≃ Ray(Λ^max N)`: the orientation of `f` at `x` and
the induced orientation of `ker L` determine each other. -/
def orKerEquiv (hf : B.IsScFredholmSection f) {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f)
    (hLs : Function.Surjective L) {N : Submodule ℝ (p.c.φ.model.E 0)}
    (hN : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N) :
    p.Or f hf ≃ Module.Ray ℝ (maxPow N) :=
  (p.orEquivRay hf hL).trans (surjRay hLs p.T.subtypeL Subtype.val_injective hN)

theorem orKerEquiv_apply (hf : B.IsScFredholmSection f) {L : ↥p.T →L[ℝ] ↥p.K}
    (hL : L ∈ p.linSet f) (hLs : Function.Surjective L) {N : Submodule ℝ (p.c.φ.model.E 0)}
    (hN : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N) (o : p.Or f hf) :
    p.orKerEquiv hf hL hLs hN o = p.orKer o hL hLs hN := rfl

/-- For an onto member of `Lin(f, x)` the kernel is finite-dimensional. -/
theorem finiteDimensional_of_mem_linSet (hf : B.IsScFredholmSection f)
    {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) {N : Submodule ℝ (p.c.φ.model.E 0)}
    (hN : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N) : FiniteDimensional ℝ N := by
  have := (p.isFredholm_of_mem_linSet hf L hL).finite_ker
  exact (kerEquivOfMap L p.T.subtypeL Subtype.val_injective hN).finiteDimensional

/-- **The induced orientation of `ker L` as an orientation of the subspace `N`** (`pullOr` along
the identity): the bases of `N` positive for it are those whose wedge lies in `orKer o`. -/
def orKerOrientation (o : p.Or f hf) {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f)
    (hLs : Function.Surjective L) {N : Submodule ℝ (p.c.φ.model.E 0)}
    (hN : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N) [FiniteDimensional ℝ N] {k : ℕ}
    (hk : finrank ℝ N = k) : Orientation ℝ N (Fin k) :=
  pullOr hk (LinearEquiv.refl ℝ N) (p.orKer o hL hLs hN)

/-- **The characterization of `orKerOrientation`**: a basis `b` of `N` is positive iff
`b₁ ∧ … ∧ b_k` lies in the ray `orKer o`. -/
theorem orientation_eq_orKerOrientation_iff (o : p.Or f hf) {L : ↥p.T →L[ℝ] ↥p.K}
    (hL : L ∈ p.linSet f) (hLs : Function.Surjective L) {N : Submodule ℝ (p.c.φ.model.E 0)}
    (hN : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N) [FiniteDimensional ℝ N] {k : ℕ}
    (hk : finrank ℝ N = k) (b : Basis (Fin k) ℝ N) :
    b.orientation = p.orKerOrientation o hL hLs hN hk ↔
      p.orKer o hL hLs hN = rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk (LinearEquiv.refl ℝ N) b) :=
  orientation_eq_pullOr_iff hk _ _ b

/-- `o ↦ orKerOrientation o` is injective: the orientation of `f` at `x` is recovered from the
induced orientation of `ker L`. -/
theorem orKerOrientation_injective (hf : B.IsScFredholmSection f) {L : ↥p.T →L[ℝ] ↥p.K}
    (hL : L ∈ p.linSet f) (hLs : Function.Surjective L) {N : Submodule ℝ (p.c.φ.model.E 0)}
    (hN : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N) [FiniteDimensional ℝ N] {k : ℕ}
    (hk : finrank ℝ N = k) {o o' : p.Or f hf}
    (h : p.orKerOrientation o hL hLs hN hk = p.orKerOrientation o' hL hLs hN hk) : o = o' := by
  apply (p.orKerEquiv hf hL hLs hN).injective
  rw [orKerEquiv_apply, orKerEquiv_apply]
  set b := pullBasis (E := N) hk
  have h1 := (p.orientation_eq_orKerOrientation_iff o hL hLs hN hk b)
  have h2 := (p.orientation_eq_orKerOrientation_iff o' hL hLs hN hk b)
  rcases b.orientation_eq_or_eq_neg (p.orKerOrientation o hL hLs hN hk) with e | e
  · rw [h1.1 e.symm, h2.1 (e.symm.trans h)]
  · have e0 : b.orientation = -p.orKerOrientation o hL hLs hN hk := by
      rw [e, neg_neg]
    have e' : b.orientation = -p.orKerOrientation o' hL hLs hN hk := by rw [← h]; exact e0
    have hneg : ∀ o₁ : p.Or f hf, b.orientation = -p.orKerOrientation o₁ hL hLs hN hk →
        p.orKer o₁ hL hLs hN =
          -rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk (LinearEquiv.refl ℝ N) b) := by
      intro o₁ he
      have hd : finrank ℝ (maxPow N) = 1 := finrank_maxPow
      rcases ray_eq_or_eq_neg_of_finrank_eq_one hd
        (wedge_equiv_ne_zero hk (LinearEquiv.refl ℝ N) b) (p.orKer o₁ hL hLs hN) with r | r
      · have h' := (p.orientation_eq_orKerOrientation_iff o₁ hL hLs hN hk b).2 r
        exact absurd (h'.symm.trans he) (Module.Ray.ne_neg_self _)
      · exact r
    rw [hneg o e0, hneg o' e']

end ChartPoint

end Polyfold
