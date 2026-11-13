import Polyfold.Chapter13.MultisectionSupport

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.2 (pp. 611–612): the convolution of finitely many sc⁺-multisections over the fibres, the
functor underlying the sums of Definition 13.2.9 and Lemma 13.2.13.

# Finite convolutions of sc⁺-multisections

For a finite family `(Λᵢ)_{i ∈ ι}` of functions `W → ℚ⁺` the convolution over the fibre `W_x` is
`(⊕ᵢ Λᵢ)(w) = ∑_{(vᵢ) ∈ W_x^ι, ∑ vᵢ = w} ∏ᵢ Λᵢ(vᵢ)` (`convAt`, `conv`; the two-term case is the
formula (1) of Definition 13.2.9, and the locally finite sums before Lemma 13.2.13 are locally of
this form).

## Main statements (namespace `Polyfold.SBLocalization`)

* `convAt_eq_sum`: if each `Λᵢ` is given over `W_x` by finitely many points `aᵢ(k)` with weights
  `σᵢ(k)`, then `(⊕ᵢ Λᵢ)(w) = ∑_{κ} [∑ᵢ aᵢ(κᵢ) = w] ∏ᵢ σᵢ(κᵢ)`.
* `convAt_map`: the convolution is transported by linear isomorphisms of the fibres preserving
  every `Λᵢ`; `isWFunctor_conv`: the convolution of functors is a functor.
* `isLocalRepOn_conv`, `isScPlusMultisection_conv`: the convolution of finitely many
  sc⁺-multisections is an sc⁺-multisection, with the local sections `∑ᵢ s^i_{κᵢ}` and the weights
  `∏ᵢ σ^i_{κᵢ}` on the intersection of the domains.
* `isLocalRepOn_of_fintype`: local representations may be indexed by any finite type.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle

variable {A : SEP.{u}}

/-! ### Transport between fibres -/

/-- A function of the points of the fibres only depends on the point. -/
theorem fib_congr {α : Sort*} (F : ∀ x : A.Obj, A.P ⁻¹' {x} → α) {x x' : A.Obj} (h : x = x')
    (u : A.P ⁻¹' {x}) (u' : A.P ⁻¹' {x'}) (hu : (u : A.W) = u') : F x u = F x' u' := by
  subst h
  exact congrArg (F x) (Subtype.ext hu)

/-- The point `w` of `W` as a point of its fibre `W_{P(w)}`. -/
def toFib (w : A.W) : A.P ⁻¹' {A.P w} := ⟨w, rfl⟩

/-! ### Local representations indexed by a finite type -/

/-- A local representation indexed by any finite type gives one indexed by `Fin k`
(Definition 13.2.1 numbers the local sections `s₁, …, s_k`). -/
theorem isLocalRepOn_of_fintype {Λ : A.W → ℚ≥0} {O : Set A.Obj} {K : Type*} [Fintype K]
    (S : K → A.Obj → A.W) (τ : K → ℚ≥0) (hpos : ∀ κ, 0 < τ κ)
    (hS : ∀ κ, IsScPlusSectionOn A (S κ) O) (hsum : ∑ κ, τ κ = 1)
    (hrep : ∀ w, A.P w ∈ O → Λ w = ∑ κ, if w = S κ (A.P w) then τ κ else 0) :
    IsLocalRepOn A Λ O (fun n => S ((Fintype.equivFin K).symm n))
      (fun n => τ ((Fintype.equivFin K).symm n)) := by
  set e := Fintype.equivFin K
  refine ⟨fun n => hpos _, fun n => hS _, ?_, fun w hw => ?_⟩
  · rw [← hsum]; exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
  · rw [hrep w hw]
    exact (Fintype.sum_equiv e.symm _ _ fun _ => rfl).symm

/-! ### The convolution over a fibre -/

/-- **The convolution over the fibre `W_x`**: `(⊕ᵢ Λᵢ)(w) = ∑_{(vᵢ) ∈ W_x^ι, ∑ vᵢ = w} ∏ᵢ Λᵢ(vᵢ)`
(a `finsum`; it is a finite sum for sc⁺-multisections, `convAt_eq_sum`). -/
def convAt {ι : Type*} [Fintype ι] (Λ : ι → A.W → ℚ≥0) (x : A.Obj) (w : A.W) : ℚ≥0 :=
  ∑ᶠ v : ι → A.P ⁻¹' {x},
    if ((∑ i, v i : A.P ⁻¹' {x}) : A.W) = w then ∏ i, Λ i (v i) else 0

/-- **The convolution `⊕ᵢ Λᵢ : W → ℚ⁺`** of a finite family, over the fibre of `P(w)`. -/
def conv {ι : Type*} [Fintype ι] (Λ : ι → A.W → ℚ≥0) (w : A.W) : ℚ≥0 :=
  convAt Λ (A.P w) w

theorem conv_eq_convAt {ι : Type*} [Fintype ι] (Λ : ι → A.W → ℚ≥0) {x : A.Obj} {w : A.W}
    (hw : A.P w = x) : conv Λ w = convAt Λ x w := by
  unfold conv; rw [hw]

/-- **The convolution over a fibre, from finite descriptions of the factors**: if over `W_x` each
`Λᵢ` is `u ↦ ∑_k [u = aᵢ(k)] σᵢ(k)`, then
`(⊕ᵢ Λᵢ)(w) = ∑_{κ ∈ Πᵢ Kᵢ} [∑ᵢ aᵢ(κᵢ) = w] ∏ᵢ σᵢ(κᵢ)`. -/
theorem convAt_eq_sum {ι : Type*} [Fintype ι] {K : ι → Type*} [∀ i, Fintype (K i)]
    {Λ : ι → A.W → ℚ≥0} {x : A.Obj} (a : ∀ i, K i → A.P ⁻¹' {x}) (σ : ∀ i, K i → ℚ≥0)
    (hΛ : ∀ i (u : A.P ⁻¹' {x}), Λ i u = ∑ k, if u = a i k then σ i k else 0) (w : A.W) :
    convAt Λ x w = ∑ κ : (∀ i, K i),
      if ((∑ i, a i (κ i) : A.P ⁻¹' {x}) : A.W) = w then ∏ i, σ i (κ i) else 0 := by
  have hprod : ∀ v : ι → A.P ⁻¹' {x}, ∏ i, Λ i (v i) =
      ∑ κ : (∀ i, K i), if v = (fun i => a i (κ i)) then ∏ i, σ i (κ i) else 0 := fun v => by
    simp_rw [hΛ]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun κ _ => ?_
    by_cases hv : v = fun i => a i (κ i)
    · subst hv
      rw [if_pos rfl]
      exact Finset.prod_congr rfl fun i _ => if_pos rfl
    · rw [if_neg hv]
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ a i (κ i) := by
        by_contra hne
        push Not at hne
        exact hv (funext hne)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  have hterm : ∀ v : ι → A.P ⁻¹' {x},
      (if ((∑ i, v i : A.P ⁻¹' {x}) : A.W) = w then ∏ i, Λ i (v i) else 0) =
      ∑ κ : (∀ i, K i), if v = (fun i => a i (κ i)) then
        (if ((∑ i, a i (κ i) : A.P ⁻¹' {x}) : A.W) = w then ∏ i, σ i (κ i) else 0) else 0 :=
    fun v => by
      rw [hprod v]
      split_ifs with hc
      · refine Finset.sum_congr rfl fun κ _ => ?_
        split_ifs with h1 h2
        · rfl
        · subst h1; exact absurd hc h2
        · rfl
      · refine (Finset.sum_eq_zero fun κ _ => ?_).symm
        split_ifs with h1 h2
        · subst h1; exact absurd h2 hc
        · rfl
        · rfl
  unfold convAt
  simp_rw [hterm]
  rw [finsum_sum_comm]
  · refine Finset.sum_congr rfl fun κ _ => ?_
    rw [finsum_eq_single _ (fun i => a i (κ i)) fun v hv => if_neg hv, if_pos rfl]
  · intro κ _
    refine (finite_singleton (fun i => a i (κ i))).subset fun v hv => ?_
    by_contra hne
    exact hv (if_neg hne)

/-- **Transport of the convolution between fibres**: a linear isomorphism `e : W_x → W_y`
preserving every `Λᵢ` carries `(⊕ᵢ Λᵢ)` over `W_x` to `(⊕ᵢ Λᵢ)` over `W_y`. -/
theorem convAt_map {ι : Type*} [Fintype ι] {Λ : ι → A.W → ℚ≥0} {x y : A.Obj}
    (e : A.P ⁻¹' {x} ≃ₗ[ℝ] A.P ⁻¹' {y}) (he : ∀ i (u : A.P ⁻¹' {x}), Λ i (e u) = Λ i u)
    (u : A.P ⁻¹' {x}) : convAt Λ x u = convAt Λ y (e u) := by
  unfold convAt
  rw [← finsum_comp_equiv (Equiv.arrowCongr (Equiv.refl ι) e.toEquiv)]
  refine finsum_congr fun v => ?_
  have hs : (∑ i, (Equiv.arrowCongr (Equiv.refl ι) e.toEquiv v) i : A.P ⁻¹' {y}) =
      e (∑ i, v i) := by
    rw [map_sum]; rfl
  have hp : ∏ i, Λ i ((Equiv.arrowCongr (Equiv.refl ι) e.toEquiv v) i : A.P ⁻¹' {y}) =
      ∏ i, Λ i (v i) := Finset.prod_congr rfl fun i _ => he i (v i)
  rw [hs, hp]
  refine if_congr ?_ rfl rfl
  rw [← Subtype.ext_iff, ← Subtype.ext_iff]
  exact e.injective.eq_iff.symm

/-- **The convolution of functors is a functor** (the fibre maps `μ(φ, ·)` are linear
isomorphisms, `EpStrongBundle.fiberMorEquiv`). -/
theorem isWFunctor_conv {ι : Type*} [Fintype ι] {Λ : ι → A.W → ℚ≥0}
    (hΛ : ∀ i, IsWFunctor A (Λ i)) : IsWFunctor A (conv Λ) := by
  rintro ⟨⟨φ, w⟩, hq⟩
  have hq' : A.P w = A.X.src φ := hq
  set e := (A.E.fiberMorEquiv φ).toLinearEquiv
  have he : ∀ i (u : A.P ⁻¹' {A.X.src φ}), Λ i (e u) = Λ i u := fun i u =>
    hΛ i ⟨(φ, (u : A.W)), u.2⟩
  have h1 := convAt_map e he ⟨w, hq'⟩
  rw [conv_eq_convAt Λ hq', conv_eq_convAt Λ (A.E.P_μ _)]
  exact (h1.trans (congrArg _ (A.E.μ_congr rfl))).symm

/-- Over a point `x ∈ O` of a local representation, `Λ` is given on the fibre `W_x` by the finitely
many points `sᵢ(x)` with the weights `σᵢ`. -/
theorem IsLocalRepOn.apply_fib {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ) {x : A.Obj}
    (hx : x ∈ O) (u : A.P ⁻¹' {x}) :
    Λ u = ∑ i, if u = (⟨s i x, (h.2.1 i).1 x hx⟩ : A.P ⁻¹' {x}) then σ i else 0 := by
  rw [h.apply_of_proj hx u.2]
  refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
  exact ⟨fun e => Subtype.ext e, fun e => by rw [e]⟩

/-- **The local representation of a finite convolution**: if each `Λᵢ` has the local
representation `(sⁱ_k, σⁱ_k)` on `O`, with global sections `sⁱ_k`, then `⊕ᵢ Λᵢ` is given on `O` by
the sections `∑ᵢ sⁱ_{κᵢ}` with the weights `∏ᵢ σⁱ_{κᵢ}`, `κ ∈ Πᵢ Fin kᵢ`. -/
theorem conv_eq_sum_of_isLocalRepOn {ι : Type*} [Fintype ι] {Λ : ι → A.W → ℚ≥0}
    {O : Set A.Obj} {k : ι → ℕ} {s : ∀ i, Fin (k i) → A.Obj → A.W} {σ : ∀ i, Fin (k i) → ℚ≥0}
    (h : ∀ i, IsLocalRepOn A (Λ i) O (s i) (σ i)) (hs : ∀ i j, IsSection A.P (s i j))
    {w : A.W} (hw : A.P w ∈ O) :
    conv Λ w = ∑ κ : (∀ i, Fin (k i)),
      if w = sectionSum A.P Finset.univ (fun i => s i (κ i)) (A.P w) then ∏ i, σ i (κ i)
      else 0 := by
  rw [conv, convAt_eq_sum (fun i j => ⟨s i j (A.P w), (h i).2.1 j |>.1 _ hw⟩) σ
    (fun i u => (h i).apply_fib hw u) w]
  refine Finset.sum_congr rfl fun κ _ => if_congr ?_ rfl rfl
  rw [sectionSum_apply (fun i => hs i (κ i))]
  exact eq_comm

/-- **The convolution of finitely many sc⁺-multisections has a local representation on the
intersection of the domains** (the sections `∑ᵢ sⁱ_{κᵢ}`, the weights `∏ᵢ σⁱ_{κᵢ}`). -/
theorem isLocalRepOn_conv {ι : Type*} [Fintype ι] {Λ : ι → A.W → ℚ≥0} {O : Set A.Obj}
    (hO : IsOpen O) {k : ι → ℕ} {s : ∀ i, Fin (k i) → A.Obj → A.W} {σ : ∀ i, Fin (k i) → ℚ≥0}
    (h : ∀ i, IsLocalRepOn A (Λ i) O (s i) (σ i)) :
    ∃ (N : ℕ) (S : Fin N → A.Obj → A.W) (τ : Fin N → ℚ≥0), IsLocalRepOn A (conv Λ) O S τ := by
  -- normalize the local sections to global sections of `P`
  set s' : ∀ i, Fin (k i) → A.Obj → A.W := fun i j => extendZero O (s i j)
  have h' : ∀ i, IsLocalRepOn A (Λ i) O (s' i) (σ i) := fun i => (h i).extendZero
  have hs' : ∀ i j, IsSection A.P (s' i j) := fun i j => isSection_extendZero _ _
  refine ⟨_, _, _, isLocalRepOn_of_fintype (K := ∀ i, Fin (k i))
    (fun κ => sectionSum A.P Finset.univ (fun i => s' i (κ i))) (fun κ => ∏ i, σ i (κ i))
    (fun κ => Finset.prod_pos fun i _ => (h i).1 _)
    (fun κ => isScPlusSectionOn_sectionSum _ hO (fun i => (h' i).2.1 (κ i)) fun i => hs' i _)
    ?_ fun w hw => conv_eq_sum_of_isLocalRepOn h' hs' hw⟩
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  exact Finset.prod_eq_one fun i _ => (h i).2.2.1

/-- **The convolution of finitely many sc⁺-multisections is an sc⁺-multisection** (the functor of
the finite sums `⊕_{j ∈ J} Λ_j`, pp. 611–612). -/
theorem isScPlusMultisection_conv {ι : Type*} [Fintype ι] {Λ : ι → A.W → ℚ≥0}
    (hΛ : ∀ i, IsScPlusMultisection A (Λ i)) : IsScPlusMultisection A (conv Λ) := by
  refine ⟨isWFunctor_conv fun i => (hΛ i).1, fun x => ?_⟩
  choose R k s σ h using fun i => (hΛ i).2 x
  set O := ⋂ i, (R i).U
  have hO : IsOpen O := isOpen_iInter_of_finite fun i => (R i).isOpen_U
  have hxO : x ∈ O := mem_iInter.2 fun i => (R i).mem_U
  obtain ⟨N, S, τ, hrep⟩ := isLocalRepOn_conv hO fun i =>
    (h i).mono hO (iInter_subset _ i)
  exact hasLocalSectionStructure_of_isLocalRepOn hO hxO hrep

end SBLocalization

end Polyfold
