import Polyfold.Chapter13.P3A_Atomic
import Polyfold.Chapter12.P3S_ScPlusSectionFunctor

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.5, **Theorem 13.5.4** (Construction I, p. 632), **Theorem 13.5.5** (Construction II,
p. 633) and **Theorem 13.5.6** (p. 634) (2017: Theorems 13.7–13.9).

# Constructions of atomic sc⁺-multisections

## The text, paraphrased

(Theorem 13.5.4) Let `X` admit sc-smooth bump functions, `x` be smooth, `U(x)` a `G_x`-invariant
open neighbourhood with the natural action and the properness property, `V(x)` open and
`G_x`-invariant with `cl V(x) ⊆ U(x)`.  (1) For a smooth `w ∈ W_x` there are finitely many
sc⁺-sections `(sᵢ)_{i ∈ I}` on `U(x)` vanishing on `U(x) ∖ V(x)`, an action of `G_x` on `I` with
`s_{g(i)}(g ∗ z) = μ(Γ(g, z), sᵢ(z))`, and `s_{i₀}(x) = w`.  (2) For an sc⁺-section `s` near `x`
the same, supported in `U(x)`, with `s_{i₀} = s` near `x`.  *Proof*: a local section `s₀` (cut
off by a bump function), `I = G_x`, `s_g(g ∗ z) = μ(Γ(g, z), s₀(z))`.

(Theorem 13.5.5) For finitely many sc⁺-sections `(sᵢ)_{i ∈ I}` of `W → X` supported in `U(x)`
with a `G_x`-action on `I` and `s_{g(i)}(g ∗ z) = μ(Γ(g, z), sᵢ(z))` there is a unique atomic
sc⁺-multisection `Λ`, supported in the saturation of `U(x)`, with
`Λ(w) = |I|⁻¹·#{i | sᵢ(P(w)) = w}` over `U(x)`; it is structurable.

(Theorem 13.5.6) Let `|X|` be paracompact, `X` admit sc-smooth bump functions and `N` be an
auxiliary norm.  For a smooth `w ∈ W ∖ 0` over `x` and `U(x)` with the natural action there is an
atomic `Λ` with (1) `dom-supp(Λ) ⊆ π⁻¹(U(x))`, (2) `Λ(g ∗ w) > 0` for `g ∈ G_x`.  For an
sc⁺-section `s` on `U(x)` and `ε > 0` there is an atomic `Λ` supported in `π⁻¹(U(x))` with
`N(Λ)(y) ≤ N(s(x)) + ε` for all `y`, whose local section structure near `x` contains `s` with
positive weight.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `SymmetricFamily A R`: the input of Theorem 13.5.5 (global sc⁺-sections supported in
  `U(x) = R.U`, equivariant on `U(x)`).
* `SymmetricFamily.exists_vanishing_nbhd`: the `V(x)` of the proof of Theorem 13.5.5 (an open
  `G_x`-invariant `V(x) ∋ x` with `cl V(x) ⊆ U(x)` off which all `sᵢ` vanish);
  `AtomicData.ofFamily`.
* **`theorem_13_5_5`**: existence and uniqueness of `Λ`, as printed (without "structurable",
  see `P3A_AtomicStructurable.lean`).
* `SymmetricFamily.ofSeed`: the family `s_g = μ(Γ(g, ·), s₀(·))` of the proof of Theorem 13.5.4
  (the translates `natTerm` of `P3S_ScPlusSectionFunctor.lean`), `ofSeed_one`, `ofSeed_vanish`,
  `ofSeed_normW_le`.
* **`theorem_13_5_4_1`**, **`theorem_13_5_4_2`**: Construction I (1), (2).
* `normW_μ`, `AtomicData.pointwiseNorm_mult_le`: the pointwise norm of an atomic multisection is
  bounded by the norms of its sections.
* **`theorem_13_5_6_1`**, **`theorem_13_5_6_2`** and `theorem_13_5_6`: Theorem 13.5.6.

## Reading

* "Admits sc-smooth bump functions" is `AdmitsBumpFunctionsPointwise` (the reading of Theorem
  12.3.3, `P3S_BumpEp.lean`); Theorem 13.5.5 does not use it, nor the smoothness of `x`.
* "`Λ` supported in the saturation of `U(x)`" (Theorem 13.5.5) is: `Λ(w) = 1` for `w = 0` and `0`
  otherwise, over points not isomorphic to a point of `U(x)`.  "`π⁻¹(U(x))`" in Theorem 13.5.6 is
  the saturation `π⁻¹(π(U(x)))`; `g ∗ w` is `μ(g, w)`.
* Theorem 13.5.5 needs `I ≠ ∅` (an sc⁺-multisection has weights summing to `1`): assumed.
* "Contains `s` with a positive weight" (Theorem 13.5.6): a local representation of `Λ` on an
  open `O ∋ x` (Definition 13.2.1) one of whose sections equals `s` on `O`.
* `N(s(x))` is `normW N (s x)` (`N` read on `W`, `P3M_MultisectionSupport.lean`); `|X|`
  paracompact is kept as in the text and not used (the text uses it for the existence of `N`,
  which is a hypothesis).
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

/-! ### Auxiliary norms read on `W` -/

/-- `μ` maps `𝐗 ₛ×_P W_{0,1}` into `W_{0,1}`. -/
theorem mem_oneSet_μ {φ : A.Mor} {w : A.W} (h : A.P w = A.X.src φ) (hw : w ∈ A.B.oneSet) :
    A.E.μ ⟨(φ, w), h⟩ ∈ A.B.oneSet := by
  obtain ⟨h1, he⟩ := A.E.exists_oneVal_eq_μ (A.B.oneMk w hw) φ (by rw [A.B.oneVal_oneMk]; exact h)
  have : A.E.μ ⟨(φ, w), h⟩ = A.B.oneVal h1 :=
    (A.E.μ_congr (Prod.ext rfl (A.B.oneVal_oneMk w hw).symm)).trans he.symm
  rw [this]; exact A.B.oneVal_mem h1

theorem mem_oneSet_of_μ {φ : A.Mor} {w : A.W} (h : A.P w = A.X.src φ)
    (hw : A.E.μ ⟨(φ, w), h⟩ ∈ A.B.oneSet) : w ∈ A.B.oneSet := by
  have hP : A.P (A.E.μ ⟨(φ, w), h⟩) = A.X.src (A.X.inv φ) := by
    rw [A.E.P_μ]; exact (A.X.src_inv _).symm
  have e : A.E.μ ⟨(A.X.inv φ, A.E.μ ⟨(φ, w), h⟩), hP⟩ = w := A.E.μ_inv_μ ⟨(φ, w), h⟩ hP
  rw [← e]
  exact mem_oneSet_μ _ hw

/-- **`N(μ(φ, w)) = N(w)`** for an auxiliary norm of `(P, μ)` (Definition 8.3.5 (3)). -/
theorem normW_μ {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N) {φ : A.Mor} {w : A.W}
    (h : A.P w = A.X.src φ) (hw : w ∈ A.B.oneSet) :
    normW N (A.E.μ ⟨(φ, w), h⟩) = normW N w := by
  obtain ⟨h1, he⟩ := A.E.exists_oneVal_eq_μ (A.B.oneMk w hw) φ (by rw [A.B.oneVal_oneMk]; exact h)
  have hμ : A.E.μ ⟨(φ, w), h⟩ = A.B.oneVal h1 :=
    (A.E.μ_congr (Prod.ext rfl (A.B.oneVal_oneMk w hw).symm)).trans he.symm
  have hm := mem_oneSet_μ h hw
  rw [normW_of_mem N hm, normW_of_mem N hw]
  have e : A.B.oneMk _ hm = h1 := A.B.oneVal_injective (by rw [A.B.oneVal_oneMk, hμ])
  rw [e]
  exact hN.map_μ h1 _ φ _ he

theorem fiberZero_mem_oneSet (y : A.Obj) : fiberZero A.P y ∈ A.B.oneSet :=
  (StrongBundle.isScPlusSection_fiberZero (B := A.B)).mem_oneSet y

theorem normW_fiberZero {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) (y : A.Obj) :
    normW N (fiberZero A.P y) = 0 :=
  (normW_eq_zero_iff hN (fiberZero_mem_oneSet y)).2 (by rw [proj_fiberZero A.P])

/-! ### Theorem 13.5.5 (Construction II) -/

/-- **The input of Theorem 13.5.5** (p. 633): finitely many sc⁺-sections `(sᵢ)_{i ∈ I}` of
`W → X` (over the object M-polyfold) supported in `U(x) = R.U`, an action of `G_x` on `I`, and
`s_{g(i)}(g ∗ z) = μ(Γ(g, z), sᵢ(z))` for `z ∈ U(x)`. -/
structure SymmetricFamily (A : SEP.{u}) {x : A.Obj} (R : A.X.NaturalRep x) where
  /-- The index set. -/
  I : Type u
  [fintype : Fintype I]
  [mulAction : MulAction (A.X.Isotropy x) I]
  /-- The sections. -/
  s : I → A.Obj → A.W
  isScPlusSection : ∀ i, A.B.IsScPlusSection (s i)
  support_subset : ∀ i, sectionSupport A.P (s i) ⊆ R.U
  equivariant : ∀ (g : A.X.Isotropy x) (i : I) (y : A.Obj) (hy : y ∈ R.U),
    s (g • i) (R.Φ g y) =
      A.E.μ ⟨(R.Γ g y, s i y), ((isScPlusSection i).1 y).trans (R.src_Γ g y hy).symm⟩

attribute [instance] SymmetricFamily.fintype SymmetricFamily.mulAction

namespace SymmetricFamily

variable {x : A.Obj} {R : A.X.NaturalRep x} (F : SymmetricFamily A R)

/-- `sᵢ(y) = 0` iff `s_{g(i)}(g ∗ y) = 0`. -/
theorem eq_zero_iff (g : A.X.Isotropy x) (i : F.I) {y : A.Obj} (hy : y ∈ R.U) :
    F.s (g • i) (R.Φ g y) = fiberZero A.P (R.Φ g y) ↔ F.s i y = fiberZero A.P y := by
  rw [F.equivariant g i y hy]
  have h0 : A.P (fiberZero A.P y) = A.X.src (R.Γ g y) := by
    rw [proj_fiberZero A.P, R.src_Γ g y hy]
  have hz : A.E.μ ⟨(R.Γ g y, fiberZero A.P y), h0⟩ = fiberZero A.P (R.Φ g y) := by
    have e := μ_fiberZero A (R.Γ g y) (isSection_fiberZero _)
    rw [R.tgt_Γ g y hy] at e
    have e2 : A.E.μ ⟨(R.Γ g y, fiberZero A.P y), h0⟩ =
        A.E.μ ⟨(R.Γ g y, fiberZero A.P (A.X.src (R.Γ g y))), isSection_fiberZero _⟩ :=
      A.E.μ_congr (Prod.ext rfl (congrArg (fiberZero A.P) (R.src_Γ g y hy).symm))
    exact e2.trans e
  rw [← hz]
  constructor
  · exact EpStrongBundle.μ_injective_snd A.E _ h0
  · intro e
    exact A.E.μ_congr (Prod.ext rfl e)

/-- **The `V(x)` of the proof of Theorem 13.5.5** ((ii), p. 633): an open `G_x`-invariant
`V(x) ∋ x` with `cl V(x) ⊆ U(x)` such that every `sᵢ` vanishes off `V(x)`. -/
theorem exists_vanishing_nbhd :
    ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ (∀ g, MapsTo (R.Φ g) V V) ∧ closure V ⊆ R.U ∧
      ∀ i y, y ∉ V → F.s i y = fiberZero A.P y := by
  set K : Set A.Obj := {x} ∪ ⋃ i, sectionSupport A.P (F.s i) with hK
  have hKc : IsClosed K := isClosed_singleton.union
    (isClosed_iUnion_of_finite fun i => isClosed_closure)
  have hKU : K ⊆ R.U :=
    union_subset (singleton_subset_iff.2 R.mem_U) (iUnion_subset F.support_subset)
  obtain ⟨V₀, hV₀o, hKV₀, hV₀cl⟩ := normal_exists_closure_subset hKc R.isOpen_U hKU
  set V : Set A.Obj := ⋂ g, R.U ∩ R.Φ g ⁻¹' V₀ with hVdef
  have hVo : IsOpen V := isOpen_iInter_of_finite fun g =>
    (R.continuousOn_Φ g).isOpen_inter_preimage R.isOpen_U hV₀o
  have hVV₀ : V ⊆ V₀ := fun y hy => by
    have := (mem_iInter.1 hy 1).2
    rwa [mem_preimage, R.Φ_one y (mem_iInter.1 hy 1).1] at this
  refine ⟨V, hVo, mem_iInter.2 fun g => ⟨R.mem_U, by
    rw [mem_preimage, R.Φ_self]; exact hKV₀ (mem_union_left _ rfl)⟩, fun h y hy => mem_iInter.2
    fun g => ⟨R.mapsTo_Φ h (mem_iInter.1 hy 1).1, ?_⟩, (closure_mono hVV₀).trans hV₀cl,
    fun i y hy => ?_⟩
  · rw [mem_preimage, ← R.Φ_mul g h y (mem_iInter.1 hy 1).1]
    exact (mem_iInter.1 hy (g * h)).2
  · by_cases hyU : y ∈ R.U
    · obtain ⟨g, hg⟩ : ∃ g, R.Φ g y ∉ V₀ := by
        by_contra hall
        exact hy (mem_iInter.2 fun g => ⟨hyU, not_not.1 fun h => hall ⟨g, h⟩⟩)
      have hnot : R.Φ g y ∉ sectionSupport A.P (F.s (g • i)) := fun h =>
        hg (hKV₀ (mem_union_right _ (mem_iUnion.2 ⟨g • i, h⟩)))
      exact (F.eq_zero_iff g i hyU).1 (StrongBundle.eq_fiberZero_of_notMem_sectionSupport hnot)
    · exact StrongBundle.eq_fiberZero_of_notMem_sectionSupport fun h => hyU (F.support_subset i h)

end SymmetricFamily

/-- **The atomic data of a symmetric family** with a `V(x)` as in the proof of Theorem 13.5.5. -/
def AtomicData.ofFamily {x : A.Obj} (R : A.X.NaturalRep x)
    (hprop : A.X.HasPropernessProperty R.U) (F : SymmetricFamily A R) {V : Set A.Obj}
    (hVo : IsOpen V) (hxV : x ∈ V) (hVinv : ∀ g, MapsTo (R.Φ g) V V) (hVcl : closure V ⊆ R.U)
    (hvan : ∀ i y, y ∉ V → F.s i y = fiberZero A.P y) : AtomicData A where
  x := x
  R := R
  hasPropernessProperty := hprop
  V := V
  isOpen_V := hVo
  mem_V := hxV
  mapsTo_V := hVinv
  closure_V_subset := hVcl
  I := F.I
  s := F.s
  isScPlusSectionOn i := IsScPlusSectionOn.of_isScPlusSection (F.isScPlusSection i) R.isOpen_U
  equivariant := F.equivariant
  vanish i y _ hy := hvan i y hy

/-- **2021 Theorem 13.5.5 (Construction II), p. 633 (2017: Theorem 13.8)**: for a symmetric
family `(sᵢ)_{i ∈ I}` of sc⁺-sections supported in `U(x)` (natural action, properness property),
`I ≠ ∅`, there is a **unique** atomic sc⁺-multisection `Λ` which is trivial over the points not
isomorphic to a point of `U(x)` and satisfies `Λ(w) = |I|⁻¹·#{i | sᵢ(P(w)) = w}` over `U(x)`.
(Bump functions and the smoothness of `x` are kept as in the text and not used; "structurable" is
`theorem_13_5_5_structurable_hyp`.) -/
theorem theorem_13_5_5 (_hbump : A.X.AdmitsBumpFunctionsPointwise) {x : A.Obj}
    (_hx : x ∈ A.X.PObj.smoothSet) (R : A.X.NaturalRep x) (hprop : A.X.HasPropernessProperty R.U)
    (F : SymmetricFamily A R) [Nonempty F.I] :
    ∃! Λ : A.W → ℚ≥0, IsAtomic A Λ ∧
      (∀ w, A.P w ∉ A.X.saturation R.U → Λ w = zeroMultisection A w) ∧
      ∀ w, A.P w ∈ R.U → Λ w = (Fintype.card F.I : ℚ≥0)⁻¹ *
        ((Finset.univ.filter fun i => F.s i (A.P w) = w).card : ℚ≥0) := by
  obtain ⟨V, hVo, hxV, hVinv, hVcl, hvan⟩ := F.exists_vanishing_nbhd
  set D := AtomicData.ofFamily R hprop F hVo hxV hVinv hVcl hvan
  have : Nonempty D.I := ‹Nonempty F.I›
  refine ⟨D.mult, ⟨D.isAtomic_mult, fun w hw => D.mult_eq_zeroMultisection
    fun h => hw (D.saturation_closure_V_subset h), fun w hw => D.mult_of_mem hw⟩, ?_⟩
  rintro Λ ⟨hΛ, hout, hin⟩
  funext w
  by_cases hr : D.Reach (A.P w)
  · obtain ⟨φ, hs, ht⟩ := hr
    rw [D.mult_eq hs.symm ht, ← hΛ.1.1 ⟨(φ, w), hs.symm⟩]
    exact hin _ (by rw [A.E.P_μ]; exact ht)
  · rw [D.mult_of_not_reach hr]
    exact hout w fun h => hr ((D.reach_iff_mem_saturation _).2 h)

/-! ### Theorem 13.5.4 (Construction I) -/

namespace SymmetricFamily

variable {x : A.Obj} (R : A.X.NaturalRep x) {V : Set A.Obj}

/-- **The family of the proof of Theorem 13.5.4** (p. 632): `I = G_x` acting on itself by left
multiplication, `s_g(z) = μ(Γ(g, g⁻¹ ∗ z), s₀(g⁻¹ ∗ z))` on `U(x)` (`0` off `U(x)`), for an
sc⁺-section `s₀` supported in an invariant `V(x)`, `cl V(x) ⊆ U(x)`. -/
def ofSeed (hVinv : ∀ g, MapsTo (R.Φ g) V V) (hVcl : closure V ⊆ R.U) {s₀ : A.Obj → A.W}
    (hs₀ : A.B.IsScPlusSection s₀) (hs₀V : sectionSupport A.P s₀ ⊆ V) : SymmetricFamily A R where
  I := A.X.Isotropy x
  fintype := Fintype.ofFinite _
  mulAction := Monoid.toMulAction _
  s k := EpStrongBundle.natTerm A.E R hs₀.1 k
  isScPlusSection k := EpStrongBundle.isScPlusSection_natTerm (E := A.E) R hVinv hVcl hs₀ hs₀V k
  support_subset k := by
    refine (closure_minimal (fun y hy => ?_) isClosed_closure).trans hVcl
    by_contra hyV
    exact hy (EpStrongBundle.natTerm_eq_zero (E := A.E) R hs₀.1 (subset_closure.trans hVcl)
      hVinv hs₀V k fun h => hyV (subset_closure h))
  equivariant g k y hy := by
    have e := EpStrongBundle.natTerm_tgt (E := A.E) R hs₀.1 (ψ := R.Γ g y)
      (R.Γ_mem_morOn g hy) k
    rw [R.index_Γ g hy, R.tgt_Γ g y hy] at e
    rw [smul_eq_mul, e]
    exact A.E.μ_congr (Prod.ext rfl
      (congrArg (EpStrongBundle.natTerm A.E R hs₀.1 k) (R.src_Γ g y hy)))

variable {R} (hVinv : ∀ g, MapsTo (R.Φ g) V V) (hVcl : closure V ⊆ R.U) {s₀ : A.Obj → A.W}
  (hs₀ : A.B.IsScPlusSection s₀) (hs₀V : sectionSupport A.P s₀ ⊆ V)

theorem ofSeed_s (k : A.X.Isotropy x) :
    (ofSeed R hVinv hVcl hs₀ hs₀V).s k = EpStrongBundle.natTerm A.E R hs₀.1 k := rfl

/-- `s_1 = s₀` on `U(x)`. -/
theorem ofSeed_one {y : A.Obj} (hy : y ∈ R.U) :
    (ofSeed R hVinv hVcl hs₀ hs₀V).s (1 : A.X.Isotropy x) y = s₀ y := by
  rw [ofSeed_s, EpStrongBundle.natTerm_of_mem (E := A.E) R hs₀.1 1 hy, inv_one, R.Φ_one y hy,
    R.Γ_one hy]
  exact EpStrongBundle.secAct_unit hs₀.1 y

/-- The sections vanish off `V(x)`. -/
theorem ofSeed_vanish (k : A.X.Isotropy x) {y : A.Obj} (hy : y ∉ V) :
    (ofSeed R hVinv hVcl hs₀ hs₀V).s k y = fiberZero A.P y :=
  EpStrongBundle.natTerm_eq_zero (E := A.E) R hs₀.1 (subset_closure.trans hVcl) hVinv hs₀V k hy

/-- The sections have the norms of `s₀`: `N(s_g(z)) ≤ b` if `N(s₀) ≤ b`, `b ≥ 0`. -/
theorem ofSeed_normW_le {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ y, normW N (s₀ y) ≤ b) (k : A.X.Isotropy x) (y : A.Obj) :
    normW N ((ofSeed R hVinv hVcl hs₀ hs₀V).s k y) ≤ b := by
  rw [ofSeed_s]
  by_cases hy : y ∈ R.U
  · rw [EpStrongBundle.natTerm_of_mem (E := A.E) R hs₀.1 k hy]
    unfold EpStrongBundle.secAct
    rw [normW_μ hN _ (hs₀.mem_oneSet _)]
    exact h _
  · rw [EpStrongBundle.natTerm_of_notMem (E := A.E) R hs₀.1 k hy, normW_fiberZero hN.isAuxNorm]
    exact hb

end SymmetricFamily

/-- **2021 Theorem 13.5.4 (Construction I) (1), p. 632 (2017: Theorem 13.7 (1))**: for a smooth
`x`, `U(x)` with the natural action and the properness property, an open `G_x`-invariant
`V(x) ∋ x` with `cl V(x) ⊆ U(x)` and a smooth `w ∈ W_x`, there is a symmetric family of
sc⁺-sections supported in `U(x)` (`SymmetricFamily`), vanishing off `V(x)`, with
`s_{i₀}(x) = w`.  The proof is the text's (`I = G_x`); the local section through `w` is Part I's
Lemma 5.3.3 (with a Part I auxiliary norm, Proposition 5.1.3). -/
theorem theorem_13_5_4_1 (hbump : A.X.AdmitsBumpFunctionsPointwise) {x : A.Obj}
    (hx : x ∈ A.X.PObj.smoothSet) (R : A.X.NaturalRep x) (_hprop : A.X.HasPropernessProperty R.U)
    {V : Set A.Obj} (hVo : IsOpen V) (hxV : x ∈ V) (hVinv : ∀ g, MapsTo (R.Φ g) V V)
    (hVcl : closure V ⊆ R.U) {w : A.W} (hw : w ∈ A.B.toMPolyfold0.smoothSet) (hwx : A.P w = x) :
    ∃ F : SymmetricFamily A R, (∀ i y, y ∉ V → F.s i y = fiberZero A.P y) ∧
      ∃ i₀, F.s i₀ x = w := by
  obtain ⟨N, hN⟩ := proposition_5_1_3_exists (B := A.B)
  obtain ⟨-, s₀, hs₀, hs₀x, hs₀V, -⟩ :=
    lemma_5_3_3 (EpGroupoid.theorem_12_3_2_1.1 hbump) hN hx hw hwx one_pos hVo hxV
  refine ⟨SymmetricFamily.ofSeed R hVinv hVcl hs₀ hs₀V, fun i y hy =>
    SymmetricFamily.ofSeed_vanish hVinv hVcl hs₀ hs₀V i hy, (1 : A.X.Isotropy x), ?_⟩
  rw [SymmetricFamily.ofSeed_one hVinv hVcl hs₀ hs₀V R.mem_U, hs₀x]

/-- The section `0` where `β = 0`. -/
theorem sectionSmul_eq_fiberZero {β : A.Obj → ℝ} {t : A.Obj → A.W} (ht : IsSection A.P t)
    {y : A.Obj} (hβ : β y = 0) : Polyfold.sectionSmul A.P β t y = fiberZero A.P y := by
  rw [sectionSmul_apply ht, hβ, zero_smul]; rfl

/-- **The cut-off section of the proof of Theorem 13.5.4 (2)**: for an sc⁺-section `s` on an open
`O ∋ x` and an open `V ∋ x`, `s₀ = β·s` with an sc-smooth bump `β : X → [0, 1]`, `β = 1` near `x`,
`supp β ⊆ V ∩ O` (Proposition 5.5.3) is an sc⁺-section of `W → X`, supported in `V`, equal to `s`
near `x`, vanishing off `V ∩ O`, with `N(s₀(y)) ≤ N(s(y))` on `O`. -/
theorem exists_cutoff (hbump : A.X.AdmitsBumpFunctionsPointwise) {x : A.Obj} {V O : Set A.Obj}
    (hVo : IsOpen V) (hO : IsOpen O) (hxV : x ∈ V) (hxO : x ∈ O) {s : A.Obj → A.W}
    (hs : IsScPlusSectionOn A s O) :
    ∃ s₀ : A.Obj → A.W, A.B.IsScPlusSection s₀ ∧ sectionSupport A.P s₀ ⊆ V ∧
      (∀ᶠ y in 𝓝 x, s₀ y = s y) ∧ (∀ y, y ∉ V ∩ O → s₀ y = fiberZero A.P y) ∧
      ∀ {N : A.B.One → ℝ}, A.B.IsAuxNorm N → ∀ y ∈ O, normW N (s₀ y) ≤ normW N (s y) := by
  obtain ⟨β, hβ, hβ01, -, hβsupp, hβ1⟩ :=
    proposition_5_5_3 (EpGroupoid.theorem_12_3_2_1.1 hbump) (hVo.inter hO) ⟨hxV, hxO⟩
  set t := extendZero O s with htdef
  have ht : IsSection A.P t := isSection_extendZero O s
  have htO : IsScPlusSectionOn A t O := hs.extendZero
  have hts : ∀ y ∈ O, t y = s y := fun y hy => (extendZero_eqOn hs.1 hy).symm
  set s₀ := Polyfold.sectionSmul A.P β t with hs₀def
  have hzero : ∀ y, y ∉ tsupport β → s₀ y = fiberZero A.P y := fun y hy =>
    sectionSmul_eq_fiberZero ht (image_eq_zero_of_notMem_tsupport hy)
  have hplus : A.B.IsScPlusSection s₀ := by
    obtain ⟨G₀, hG₀, hG₀f⟩ := (StrongBundle.isScPlusSection_fiberZero (B := A.B)).exists_one
    refine StrongBundle.isScPlusSection_of_locally ht.sectionSmul fun y₀ => ?_
    by_cases hy₀ : y₀ ∈ O
    · obtain ⟨-, G, hG, hGs⟩ := htO.sectionSmul hO ht hβ
      exact ⟨O, hO, hy₀, G, hGs, hG⟩
    · have hy₀' : y₀ ∉ tsupport β := fun h => hy₀ (hβsupp h).2
      exact ⟨(tsupport β)ᶜ, (isClosed_tsupport β).isOpen_compl, hy₀', G₀,
        hG₀.mono (isClosed_tsupport β).isOpen_compl (subset_univ _), fun y hy => by
          rw [hG₀f, hzero y hy]⟩
  refine ⟨s₀, hplus, ?_, ?_, fun y hy => hzero y fun h => hy (hβsupp h), fun {N} hN y hy => ?_⟩
  · refine (closure_minimal (fun y hy => ?_) (isClosed_tsupport β)).trans
      (hβsupp.trans inter_subset_left)
    by_contra h
    exact hy (hzero y h)
  · filter_upwards [hβ1, hO.mem_nhds hxO] with y hy1 hyO
    rw [hs₀def, sectionSmul_apply ht, hy1, one_smul]
    exact hts y hyO
  · -- `N(β(y)·s(y)) = |β(y)|·N(s(y)) ≤ N(s(y))`
    have hsy : s y ∈ A.B.oneSet := hs.mem_oneSet hy
    have hty : t y ∈ A.B.oneSet := by rw [hts y hy]; exact hsy
    let v : A.B.oneFiber y := ⟨⟨t y, ht y⟩, hty⟩
    have hval : s₀ y = (((β y • v : A.B.oneFiber y) : A.P ⁻¹' {y}) : A.W) := by
      rw [hs₀def, sectionSmul_apply ht, Submodule.coe_smul]
    have hs₀y : s₀ y ∈ A.B.oneSet := hplus.mem_oneSet y
    rw [normW_of_mem N hs₀y, ← hts y hy, normW_of_mem N hty]
    have e1 : A.B.oneMk (s₀ y) hs₀y = A.B.toOne (β y • v) := A.B.oneVal_injective hval
    have e2 : A.B.oneMk (t y) hty = A.B.toOne v := rfl
    rw [e1, e2, (hN.fiber y).smul, abs_of_nonneg (hβ01 y).1]
    exact mul_le_of_le_one_left (hN.nonneg _) (hβ01 y).2

/-- **2021 Theorem 13.5.4 (Construction I) (2), p. 632 (2017: Theorem 13.7 (2))**: for an
sc⁺-section `s` defined on an open neighbourhood `O` of `x`, there is a symmetric family of
sc⁺-sections supported in `U(x)` (`SymmetricFamily`), vanishing off `V(x)`, with `s_{i₀} = s` near
`x`.  The proof is the text's (`s₀ = β·s` with a concentrated bump function, `I = G_x`). -/
theorem theorem_13_5_4_2 (hbump : A.X.AdmitsBumpFunctionsPointwise) {x : A.Obj}
    (_hx : x ∈ A.X.PObj.smoothSet) (R : A.X.NaturalRep x) (_hprop : A.X.HasPropernessProperty R.U)
    {V : Set A.Obj} (hVo : IsOpen V) (hxV : x ∈ V) (hVinv : ∀ g, MapsTo (R.Φ g) V V)
    (hVcl : closure V ⊆ R.U) {O : Set A.Obj} (hO : IsOpen O) (hxO : x ∈ O) {s : A.Obj → A.W}
    (hs : IsScPlusSectionOn A s O) :
    ∃ F : SymmetricFamily A R, (∀ i y, y ∉ V → F.s i y = fiberZero A.P y) ∧
      ∃ i₀, ∀ᶠ y in 𝓝 x, F.s i₀ y = s y := by
  obtain ⟨s₀, hs₀, hs₀V, hev, -, -⟩ := exists_cutoff hbump hVo hO hxV hxO hs
  refine ⟨SymmetricFamily.ofSeed R hVinv hVcl hs₀ hs₀V, fun i y hy =>
    SymmetricFamily.ofSeed_vanish hVinv hVcl hs₀ hs₀V i hy, (1 : A.X.Isotropy x), ?_⟩
  filter_upwards [hev, R.isOpen_U.mem_nhds R.mem_U] with y hy hyU
  rw [SymmetricFamily.ofSeed_one hVinv hVcl hs₀ hs₀V hyU, hy]

/-! ### Theorem 13.5.6 -/

namespace AtomicData

variable (D : AtomicData A)

/-- **The pointwise norm of an atomic multisection** (Definition 13.2.3) is bounded by the norms
of its sections: `N(Λ)(y) ≤ b` if `N(sᵢ(z)) ≤ b` on `U(x)`, `b ≥ 0`. -/
theorem pointwiseNorm_mult_le [Nonempty D.I] {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N) {b : ℝ}
    (hb : 0 ≤ b) (hD : ∀ i, ∀ y ∈ D.R.U, normW N (D.s i y) ≤ b) (y : A.Obj) :
    pointwiseNorm N D.mult y ≤ b := by
  refine csSup_le ((D.isScPlusMultisection_mult.suppAt_nonempty y).image _) ?_
  rintro _ ⟨w, ⟨-, hpos⟩, rfl⟩
  by_cases hr : D.Reach (A.P w)
  · obtain ⟨φ, hs, ht⟩ := hr
    rw [D.mult_eq hs.symm ht, count] at hpos
    obtain ⟨i, hi⟩ : ∃ i, D.s i (A.P (A.E.μ ⟨(φ, w), hs.symm⟩)) = A.E.μ ⟨(φ, w), hs.symm⟩ := by
      by_contra hall
      rw [Finset.filter_false_of_mem fun i _ h => hall ⟨i, h⟩, Finset.card_empty, Nat.cast_zero,
        mul_zero] at hpos
      exact lt_irrefl _ hpos
    have hPm : A.P (A.E.μ ⟨(φ, w), hs.symm⟩) = A.X.tgt φ := A.E.P_μ _
    rw [hPm] at hi
    have hm1 : A.E.μ ⟨(φ, w), hs.symm⟩ ∈ A.B.oneSet := by
      rw [← hi]; exact (D.isScPlusSectionOn i).mem_oneSet ht
    rw [← normW_μ hN hs.symm (mem_oneSet_of_μ hs.symm hm1), ← hi]
    exact hD i _ ht
  · rw [D.mult_of_not_reach hr, zeroMultisection] at hpos
    split_ifs at hpos with hw
    · rw [hw, normW_fiberZero hN.isAuxNorm]; exact hb
    · exact absurd hpos (lt_irrefl _)

/-- Over `U(x)` the sections of the data form a local representation of `mult`. -/
theorem isLocalRepOn_mult [Nonempty D.I] :
    IsLocalRepOn A D.mult D.R.U (fun n => D.s ((Fintype.equivFin D.I).symm n))
      (fun _ => (Fintype.card D.I : ℚ≥0)⁻¹) := by
  have hcard : (Fintype.card D.I : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine isLocalRepOn_of_fintype (K := D.I) D.s (fun _ => (Fintype.card D.I : ℚ≥0)⁻¹)
    (fun _ => inv_pos.2 (pos_iff_ne_zero.2 hcard)) D.isScPlusSectionOn ?_ fun w hw => ?_
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard]
  · rw [D.mult_of_mem hw, count, Finset.natCast_card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : D.s i (A.P w) = w
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

end AtomicData

/-- **2021 Theorem 13.5.6, first part, p. 634 (2017: Theorem 13.9)**: for a smooth `w ∈ W ∖ 0`
over `x` and an open `U(x)` with the natural action of `G_x`, there is an atomic
sc⁺-multisection `Λ` with (1) `dom-supp(Λ) ⊆ π⁻¹(π(U(x)))` and (2) `Λ(μ(g, w)) > 0` for all
`g ∈ G_x`.  (Paracompactness and `N` are kept as in the text and not used here.) -/
theorem theorem_13_5_6_1 (_hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {N : A.B.One → ℝ} (_hN : A.E.IsAuxNorm N)
    {w : A.W} (hw : w ∈ A.B.toMPolyfold0.smoothSet) (_hw0 : w ≠ fiberZero A.P (A.P w))
    {x : A.Obj} (hwx : A.P w = x) (R : A.X.NaturalRep x) :
    ∃ Λ : A.W → ℚ≥0, IsAtomic A Λ ∧ domSupp Λ ⊆ A.X.saturation R.U ∧
      ∀ g : A.X.Isotropy x, 0 < Λ (A.E.μ ⟨(g.val, w), hwx.trans g.src_val.symm⟩) := by
  have hx : x ∈ A.X.PObj.smoothSet := by
    rw [← hwx]; exact mem_iInter.2 fun m => A.B.proj_mem_levelSet (mem_iInter.1 hw m)
  obtain ⟨R', V, hprop, hRU, hVo, hxV, hVinv, hVcl⟩ := exists_atomicNbhd x R.isOpen_U R.mem_U
  obtain ⟨F, hvan, i₀, hi₀⟩ :=
    theorem_13_5_4_1 hbump hx R' hprop hVo hxV hVinv hVcl hw hwx
  set D := AtomicData.ofFamily R' hprop F hVo hxV hVinv hVcl hvan
  have : Nonempty D.I := ⟨i₀⟩
  refine ⟨D.mult, D.isAtomic_mult, D.domSupp_mult_subset.trans
    (D.saturation_closure_V_subset.trans (preimage_mono (image_mono hRU))), fun g => ?_⟩
  rw [D.isWFunctor_mult ⟨(g.val, w), hwx.trans g.src_val.symm⟩]
  change 0 < D.mult w
  rw [D.mult_of_mem (by rw [hwx]; exact R'.mem_U), AtomicData.count]
  refine mul_pos (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)) (Nat.cast_pos.2
    (Finset.card_pos.2 ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩))
  change F.s i₀ (A.P w) = w
  rw [hwx, hi₀]

/-- **2021 Theorem 13.5.6, second part, p. 634 (2017: Theorem 13.9)**: for an auxiliary norm `N`
(Definition 8.3.5), an sc⁺-section `s` on `U(x)` (natural action) and `ε > 0`, there is an atomic
sc⁺-multisection `Λ` with `dom-supp(Λ) ⊆ π⁻¹(π(U(x)))`, `N(Λ)(y) ≤ N(s(x)) + ε` for all `y`
(Definition 13.2.3), and a local representation on an open `O ∋ x` one of whose sections is `s`
on `O`, with positive weight.  (Paracompactness is kept as in the text and not used.) -/
theorem theorem_13_5_6_2 (_hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N)
    {x : A.Obj} (R : A.X.NaturalRep x) {s : A.Obj → A.W} (hs : IsScPlusSectionOn A s R.U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Λ : A.W → ℚ≥0, IsAtomic A Λ ∧ domSupp Λ ⊆ A.X.saturation R.U ∧
      (∀ y, pointwiseNorm N Λ y ≤ normW N (s x) + ε) ∧
      ∃ (O : Set A.Obj) (k : ℕ) (s' : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0), IsOpen O ∧ x ∈ O ∧
        IsLocalRepOn A Λ O s' σ ∧ ∃ j, 0 < σ j ∧ ∀ y ∈ O, s' j y = s y := by
  set b := normW N (s x) + ε with hbdef
  have hb : 0 ≤ b := add_nonneg (normW_nonneg hN.isAuxNorm _) hε.le
  -- the open set where `N(s(y)) < N(s(x)) + ε`
  have hs' := hs
  obtain ⟨-, G, hG, hGs⟩ := hs'
  have hcont : ContinuousOn (N ∘ G) R.U :=
    hN.isAuxNorm.continuous.comp_continuousOn hGs.continuousOn
  set O₁ : Set A.Obj := R.U ∩ (N ∘ G) ⁻¹' Iio b with hO₁
  have hO₁o : IsOpen O₁ := hcont.isOpen_inter_preimage R.isOpen_U isOpen_Iio
  have hnormG : ∀ y ∈ R.U, normW N (s y) = N (G y) := fun y hy => by
    have hm : s y ∈ A.B.oneSet := by rw [← hG y hy]; exact A.B.oneVal_mem _
    rw [normW_of_mem N hm]
    congr 1
    exact A.B.oneVal_injective (by rw [A.B.oneVal_oneMk, hG y hy])
  have hxO₁ : x ∈ O₁ := ⟨R.mem_U, by
    change N (G x) < b
    rw [← hnormG x R.mem_U, hbdef]; exact lt_add_of_pos_right _ hε⟩
  -- Construction I (2) inside `O₁`
  obtain ⟨R', V, hprop, hRU, hVo, hxV, hVinv, hVcl⟩ := exists_atomicNbhd x hO₁o hxO₁
  have hR'R : R'.U ⊆ R.U := hRU.trans inter_subset_left
  have hsR' : IsScPlusSectionOn A s R'.U := hs.mono R'.isOpen_U hR'R
  obtain ⟨s₀, hs₀, hs₀V, hev, hvan₀, hnorm⟩ :=
    exists_cutoff hbump hVo R'.isOpen_U hxV R'.mem_U hsR'
  have hs₀b : ∀ y, normW N (s₀ y) ≤ b := fun y => by
    by_cases hy : y ∈ R'.U
    · refine (hnorm hN.isAuxNorm y hy).trans ?_
      rw [hnormG y (hR'R hy)]
      exact (hRU hy).2.le
    · rw [hvan₀ y fun h => hy h.2, normW_fiberZero hN.isAuxNorm]; exact hb
  set F := SymmetricFamily.ofSeed R' hVinv hVcl hs₀ hs₀V with hF
  set D := AtomicData.ofFamily R' hprop F hVo hxV hVinv hVcl
    (fun i y hy => SymmetricFamily.ofSeed_vanish hVinv hVcl hs₀ hs₀V i hy) with hD
  have : Nonempty D.I := ⟨(1 : A.X.Isotropy x)⟩
  have hDs : ∀ i, ∀ y ∈ D.R.U, normW N (D.s i y) ≤ b := fun i y _ =>
    SymmetricFamily.ofSeed_normW_le hVinv hVcl hs₀ hs₀V hN hb hs₀b i y
  refine ⟨D.mult, D.isAtomic_mult, D.domSupp_mult_subset.trans
    (D.saturation_closure_V_subset.trans (preimage_mono (image_mono hR'R))),
    D.pointwiseNorm_mult_le hN hb hDs, ?_⟩
  -- the local representation on `U'(x)` near `x` contains `s₁ = s`
  have hev' : ∀ᶠ y in 𝓝 x, D.s (1 : A.X.Isotropy x) y = s y := by
    filter_upwards [hev, R'.isOpen_U.mem_nhds R'.mem_U] with y hy hyU
    exact (SymmetricFamily.ofSeed_one hVinv hVcl hs₀ hs₀V hyU).trans hy
  obtain ⟨O', hO'sub, hO'o, hxO'⟩ := mem_nhds_iff.1 hev'
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : D.I, ∀ y ∈ R'.U ∩ O', D.s i₁ y = s y :=
    ⟨(1 : A.X.Isotropy x), fun y hy => hO'sub hy.2⟩
  refine ⟨R'.U ∩ O', _, _, _, R'.isOpen_U.inter hO'o, ⟨R'.mem_U, hxO'⟩,
    D.isLocalRepOn_mult.mono (R'.isOpen_U.inter hO'o) inter_subset_left,
    Fintype.equivFin D.I i₁, inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos), fun y hy => ?_⟩
  rw [Equiv.symm_apply_apply]
  exact hi₁ y hy

/-- **2021 Theorem 13.5.6, p. 634 (2017: Theorem 13.9)**, both parts. -/
theorem theorem_13_5_6 (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N) :
    (∀ (w : A.W), w ∈ A.B.toMPolyfold0.smoothSet → w ≠ fiberZero A.P (A.P w) →
      ∀ (R : A.X.NaturalRep (A.P w)), ∃ Λ : A.W → ℚ≥0, IsAtomic A Λ ∧
        domSupp Λ ⊆ A.X.saturation R.U ∧
        ∀ g : A.X.Isotropy (A.P w), 0 < Λ (A.E.μ ⟨(g.val, w), g.src_val.symm⟩)) ∧
    ∀ (x : A.Obj) (R : A.X.NaturalRep x) (s : A.Obj → A.W), IsScPlusSectionOn A s R.U →
      ∀ ε > 0, ∃ Λ : A.W → ℚ≥0, IsAtomic A Λ ∧ domSupp Λ ⊆ A.X.saturation R.U ∧
        (∀ y, pointwiseNorm N Λ y ≤ normW N (s x) + ε) ∧
        ∃ (O : Set A.Obj) (k : ℕ) (s' : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0), IsOpen O ∧
          x ∈ O ∧ IsLocalRepOn A Λ O s' σ ∧ ∃ j, 0 < σ j ∧ ∀ y ∈ O, s' j y = s y :=
  ⟨fun _ hw hw0 R => theorem_13_5_6_1 hpara hbump hN hw hw0 rfl R,
    fun _ R _ hs _ hε => theorem_13_5_6_2 hpara hbump hN R hs hε⟩

end SBLocalization

end Polyfold
