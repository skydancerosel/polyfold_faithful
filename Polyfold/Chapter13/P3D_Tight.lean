import Polyfold.Chapter13.P3D_Structurable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.3, pp. 618–620: the set `T_Λ`, the construction before **Proposition 13.3.15**,
**Proposition 13.3.15**, **Definition 13.3.17** (tightly structured) and **Corollary 13.3.18**
(2017: §13.3, Proposition 13.4, Definition 13.21, Corollary 13.1).

# Tightly structured sc⁺-multisections

## The text, paraphrased

`Λ` is trivial near `x` if `Λ(0_y) = 1` on a neighbourhood of `x`; `T_Λ` is the set of such
`x`.  Given `(Λ, 𝒰, S, τ)`, shrink `U(x)` for `x ∈ T_Λ` to an invariant `U'(x) ⊆ T_Λ`, replace
`sˣ` there by the single zero section on `I'_x = {∗}`, keep everything at `x ∉ T_Λ`, and replace
`τ_{x,x'}` by `[{∗} ← I_{x'} →id I_{x'}]`, `[I_x ←id I_x → {∗}]`, `[{∗} ← {∗} → {∗}]` when `x`
or `x'` lies in `T_Λ`.  (13.3.15) The result is a structured `[Λ, 𝒰', S', τ']` with these
properties.  (13.3.17) A structured multisection is tightly structured if a representative has
the properties (1)–(3) at points of `T_Λ`.  (13.3.18) Every structurable `Λ` has a tightly
structured version.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `trivialSet Λ` (`T_Λ`), `isOpen_trivialSet`, `isTrivialOn_trivialSet`, and
  `apply_fiberZero_tgt` (`Λ(0_{t(ψ)}) = Λ(0_{s(ψ)})` for a functor `Λ`).
* The new index sets `TightIdx p I = {∗ | p} ⊕ {i ∈ I | ¬p}` (so `I'_x ≃ {∗}` for `x ∈ T_Λ`
  and `I'_x ≃ I_x` otherwise, `TightIdx.eT`, `TightIdx.eN`), the structure
  `SymmetricStructureOn.tight`, the good system `Decoration.tight`, the correspondences
  `Decoration.tightτ` and `Decoration.Tau.tight` (the construction before Proposition 13.3.15;
  compatibility at `x ∈ T_Λ` holds since all sections vanish over `U(x')` near points `t(ψ)`
  with `Λ(0_{t(ψ)}) = 1`).
* **Definition 13.3.17**: `Decoration.IsTight`, `StructuredMultisection.IsTight`.
* **Proposition 13.3.15**: `proposition_13_3_15`.
* **Corollary 13.3.18**: `corollary_13_3_18`, `corollary_13_3_18_structured`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### The set `T_Λ` -/

/-- **`T_Λ`, 2021 p. 618 (2017: before Proposition 13.4)**:
the points near which `Λ` is trivial, `Λ(0_y) = 1` on a neighbourhood. -/
def trivialSet (Λ : A.W → ℚ≥0) : Set A.Obj := {x | ∃ O, IsOpen O ∧ x ∈ O ∧ IsTrivialOn Λ O}

theorem isOpen_trivialSet (Λ : A.W → ℚ≥0) : IsOpen (trivialSet Λ) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨O, hO, hxO, hT⟩
  exact ⟨O, fun y hy => ⟨O, hO, hy, hT⟩, hO, hxO⟩

theorem isTrivialOn_trivialSet (Λ : A.W → ℚ≥0) : IsTrivialOn Λ (trivialSet Λ) :=
  fun _ ⟨_, _, hxO, hT⟩ => hT _ hxO

/-- `Λ(0_{t(ψ)}) = Λ(0_{s(ψ)})` for a functor `Λ`. -/
theorem apply_fiberZero_tgt {Λ : A.W → ℚ≥0} (hΛ : IsWFunctor A Λ) (ψ : A.Mor) :
    Λ (fiberZero A.P (A.X.tgt ψ)) = Λ (fiberZero A.P (A.X.src ψ)) := by
  rw [← fibAct_fiberZero (ψ := ψ) rfl rfl, fibAct_of (proj_fiberZero A.P _)]
  exact hΛ _

/-! ### The index sets `I'_x` -/

/-- `I'_x`: one point `∗` if `p` (`x ∈ T_Λ`), and `I` if `¬p`. -/
abbrev TightIdx (p : Prop) (I : Type u) : Type u := {_a : PUnit.{u + 1} // p} ⊕ {_i : I // ¬p}

namespace TightIdx

variable {p : Prop} {I : Type u}

instance [Fintype I] : Fintype (TightIdx p I) := inferInstanceAs (Fintype (_ ⊕ _))

/-- The action: trivial on `∗`, that of `I` on `I`. -/
instance {G : Type*} [Group G] [MulAction G I] : MulAction G (TightIdx p I) where
  smul g := Sum.map id fun i : {_i : I // ¬p} => (⟨g • i.1, i.2⟩ : {_i : I // ¬p})
  one_smul := by
    rintro (κ | ⟨i, h⟩)
    · rfl
    · change (Sum.inr ⟨(1 : G) • i, h⟩ : TightIdx p I) = Sum.inr ⟨i, h⟩
      rw [one_smul]
  mul_smul g g' := by
    rintro (κ | ⟨i, h⟩)
    · rfl
    · change (Sum.inr ⟨(g * g') • i, h⟩ : TightIdx p I) = Sum.inr ⟨g • g' • i, h⟩
      rw [mul_smul]

/-- `{∗} ≃ I'_x` for `x ∈ T_Λ`. -/
def eT (hp : p) : PUnit.{u + 1} ≃ TightIdx p I where
  toFun _ := Sum.inl ⟨PUnit.unit, hp⟩
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv := by
    rintro (⟨⟨⟩, _⟩ | ⟨_, h⟩)
    · rfl
    · exact absurd hp h

/-- `I_x ≃ I'_x` for `x ∉ T_Λ`. -/
def eN (hp : ¬p) : I ≃ TightIdx p I where
  toFun i := Sum.inr ⟨i, hp⟩
  invFun := Sum.elim (fun κ => absurd κ.2 hp) Subtype.val
  left_inv _ := rfl
  right_inv := by
    rintro (⟨_, h⟩ | ⟨_, _⟩)
    · exact absurd h hp
    · rfl

theorem subsingleton (hp : p) : Subsingleton (TightIdx p I) := (eT hp).symm.subsingleton

end TightIdx

/-! ### Correspondences: relabelling -/

namespace IndexCorr

variable {α β α₀ β₀ : Type u}

theorem swap_map (e : α₀ ≃ α) (e' : β₀ ≃ β) (τ : IndexCorr α₀ β₀) :
    (τ.map e e').swap = τ.swap.map e' e :=
  ind (fun _ => rfl) τ

/-- The bi-action on a relabelled correspondence. -/
theorem biact_map {G G' : Type*} [Group G] [Group G'] [MulAction G α] [MulAction G' β]
    (g' : G') (g : G) (e : α₀ ≃ α) (e' : β₀ ≃ β) (σ : Equiv.Perm α₀) (σ' : Equiv.Perm β₀)
    (he : ∀ a, g⁻¹ • e a = e (σ a)) (he' : ∀ b, g' • e' b = e' (σ' b))
    (τ : IndexCorr α₀ β₀) : biact g' (τ.map e e') g = (τ.map σ σ').map e e' :=
  ind (fun _ => mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨(he _).symm, (he' _).symm⟩⟩) τ

theorem map_toUnit_perm [Fintype β] [Nonempty β] (σ : Equiv.Perm β) :
    (toUnit β).map (Equiv.refl _) σ = toUnit β :=
  mk_eq_mk.2 ⟨σ, fun _ => ⟨rfl, rfl⟩⟩

theorem map_fromUnit_perm [Fintype α] [Nonempty α] (σ : Equiv.Perm α) :
    (fromUnit α).map σ (Equiv.refl _) = fromUnit α :=
  mk_eq_mk.2 ⟨σ, fun _ => ⟨rfl, rfl⟩⟩

end IndexCorr

/-! ### The tight symmetric structures -/

theorem count_reindex {I I' : Type*} [Fintype I] [Fintype I'] (e : I' ≃ I)
    {s : I → A.Obj → A.W} {s' : I' → A.Obj → A.W} {y : A.Obj} (hs : ∀ κ, s' κ y = s (e κ) y)
    (w : A.W) :
    (Fintype.card I' : ℚ≥0)⁻¹ * ((Finset.univ.filter fun κ => s' κ y = w).card : ℚ≥0) =
      (Fintype.card I : ℚ≥0)⁻¹ * ((Finset.univ.filter fun i => s i y = w).card : ℚ≥0) := by
  rw [Fintype.card_congr e]
  congr 2
  exact Finset.card_equiv e fun κ => by simp [hs]

namespace SymmetricStructureOn

variable {Λ : A.W → ℚ≥0} {x : A.Obj} {N : A.X.NatNbhd x}

/-- The structure on `I'_x = TightIdx p I_x`: the zero section on `∗` (where `p`), `sˣᵢ` on `I_x`
(where `¬p`). -/
def tight (S : SymmetricStructureOn A Λ N) (hΛ : IsScPlusMultisection A Λ) (p : Prop)
    (hp : p → IsTrivialOn Λ N.U) : SymmetricStructureOn A Λ N where
  I := TightIdx p S.I
  s := Sum.elim (fun _ => fiberZero A.P) fun i : {_i : S.I // ¬p} => S.s i.1
  isScPlusSectionOn := by
    rintro (_ | i)
    · exact isScPlusSectionOn_fiberZero N.isOpen_U
    · exact S.isScPlusSectionOn i.1
  equivariant g κ y hy := by
    rcases κ with _ | i
    · exact (fibAct_fiberZero (N.src_Γ g hy) (N.tgt_Γ g hy)).symm
    · exact S.equivariant g i.1 y hy
  rep w hw := by
    by_cases hp' : p
    · rw [(ofTrivial hΛ (hp hp')).rep w hw]
      refine (count_reindex (TightIdx.eT hp').symm (fun κ => ?_) w).symm
      rcases κ with _ | ⟨_, h⟩
      · rfl
      · exact absurd hp' h
    · rw [S.rep w hw]
      refine (count_reindex (TightIdx.eN hp').symm (fun κ => ?_) w).symm
      rcases κ with ⟨_, h⟩ | _
      · exact absurd h hp'
      · rfl

end SymmetricStructureOn

/-! ### The construction before Proposition 13.3.15 -/

namespace Decoration

variable {Λ : A.W → ℚ≥0}

theorem exists_tightNbhd (D : Decoration A Λ) (x : A.Obj) :
    ∃ M : A.X.NatNbhd x, M.Le (D.𝒰.nbhd x) ∧ (x ∈ trivialSet Λ → M.U ⊆ trivialSet Λ) ∧
      (x ∉ trivialSet Λ → M = D.𝒰.nbhd x) := by
  by_cases hx : x ∈ trivialSet Λ
  · obtain ⟨M, -, hMT, hle, -⟩ := NatNbhd.exists_le_of_finite (D.𝒰.nbhd x)
      (fun e : Empty => e.elim) (isOpen_trivialSet Λ) hx
    exact ⟨M, hle, fun _ => hMT, fun h => absurd hx h⟩
  · exact ⟨_, NatNbhd.Le.refl _, fun h => absurd h hx, fun _ => rfl⟩

/-- `U'(x)`: an invariant `U'(x) ⊆ U(x) ∩ T_Λ` (same action) for `x ∈ T_Λ`, `U(x)` otherwise. -/
def tightNbhd (D : Decoration A Λ) (x : A.Obj) : A.X.NatNbhd x := (D.exists_tightNbhd x).choose

theorem tightNbhd_le (D : Decoration A Λ) (x : A.Obj) : (D.tightNbhd x).Le (D.𝒰.nbhd x) :=
  (D.exists_tightNbhd x).choose_spec.1

theorem tightNbhd_subset (D : Decoration A Λ) {x : A.Obj} (hx : x ∈ trivialSet Λ) :
    (D.tightNbhd x).U ⊆ trivialSet Λ :=
  (D.exists_tightNbhd x).choose_spec.2.1 hx

theorem tightNbhd_eq (D : Decoration A Λ) {x : A.Obj} (hx : x ∉ trivialSet Λ) :
    D.tightNbhd x = D.𝒰.nbhd x :=
  (D.exists_tightNbhd x).choose_spec.2.2 hx

/-- **The construction before Proposition 13.3.15**: `(𝒰', S')`. -/
def tight (D : Decoration A Λ) (hΛ : IsScPlusMultisection A Λ) : Decoration A Λ :=
  ⟨D.𝒰.ofSubset D.tightNbhd fun x => (D.tightNbhd_le x).subset, fun x =>
    ((D.S x).restrict (D.tightNbhd_le x)).tight hΛ (x ∈ trivialSet Λ)
      fun hx y hy => isTrivialOn_trivialSet Λ y (D.tightNbhd_subset hx hy)⟩

theorem nonempty_I (D : Decoration A Λ) (hΛ : IsScPlusMultisection A Λ) (x : A.Obj) :
    Nonempty (D.S x).I :=
  Fintype.card_pos_iff.1 ((D.S x).card_pos hΛ)

/-- **The correspondences `τ'`** (before Proposition 13.3.15). -/
def tightτ (D : Decoration A Λ) (hΛ : IsScPlusMultisection A Λ) (t : D.Tau) (x x' : A.Obj)
    (φ : A.Mor) : IndexCorr ((D.tight hΛ).S x).I ((D.tight hΛ).S x').I :=
  if hx : x ∈ trivialSet Λ then
    if hx' : x' ∈ trivialSet Λ then
      (IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1})).map (TightIdx.eT hx) (TightIdx.eT hx')
    else
      (@IndexCorr.toUnit (D.S x').I _ (D.nonempty_I hΛ x')).map (TightIdx.eT hx)
        (TightIdx.eN hx')
  else
    if hx' : x' ∈ trivialSet Λ then
      (@IndexCorr.fromUnit (D.S x).I _ (D.nonempty_I hΛ x)).map (TightIdx.eN hx)
        (TightIdx.eT hx')
    else (t.τ x x' φ).map (TightIdx.eN hx) (TightIdx.eN hx')

variable {D : Decoration A Λ} {hΛ : IsScPlusMultisection A Λ} {t : D.Tau} {x x' : A.Obj}

theorem tightτ_TT (hx : x ∈ trivialSet Λ) (hx' : x' ∈ trivialSet Λ) (φ : A.Mor) :
    D.tightτ hΛ t x x' φ =
      (IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1})).map (TightIdx.eT hx) (TightIdx.eT hx') := by
  rw [tightτ, dif_pos hx, dif_pos hx']
  rfl

theorem tightτ_TN (hx : x ∈ trivialSet Λ) (hx' : x' ∉ trivialSet Λ) (φ : A.Mor) :
    D.tightτ hΛ t x x' φ = (@IndexCorr.toUnit (D.S x').I _ (D.nonempty_I hΛ x')).map
      (TightIdx.eT hx) (TightIdx.eN hx') := by
  rw [tightτ, dif_pos hx, dif_neg hx']
  rfl

theorem tightτ_NT (hx : x ∉ trivialSet Λ) (hx' : x' ∈ trivialSet Λ) (φ : A.Mor) :
    D.tightτ hΛ t x x' φ = (@IndexCorr.fromUnit (D.S x).I _ (D.nonempty_I hΛ x)).map
      (TightIdx.eN hx) (TightIdx.eT hx') := by
  rw [tightτ, dif_neg hx, dif_pos hx']
  rfl

theorem tightτ_NN (hx : x ∉ trivialSet Λ) (hx' : x' ∉ trivialSet Λ) (φ : A.Mor) :
    D.tightτ hΛ t x x' φ = (t.τ x x' φ).map (TightIdx.eN hx) (TightIdx.eN hx') := by
  rw [tightτ, dif_neg hx, dif_neg hx']
  rfl

/-- A constant correspondence. -/
theorem isCorrespondence_const {D : Decoration A Λ} {x x' : A.Obj}
    {τ : A.Mor → IndexCorr (D.S x).I (D.S x').I} (c : IndexCorr (D.S x).I (D.S x').I)
    (hτ : ∀ φ, τ φ = c) (hb : ∀ (g' : A.X.Isotropy x') (g : A.X.Isotropy x),
      IndexCorr.biact g' c g = c)
    (hc : ∀ φ ∈ D.𝒰.mor x x', c.Sat fun i j => ∀ ψ ∈ D.𝒰.comp x x' φ, D.Compat ψ i j) :
    D.IsCorrespondence x x' τ where
  locallyConstant φ _ := Eventually.of_forall fun ψ => by rw [hτ, hτ]
  finite := (finite_singleton c).subset (by rintro _ ⟨φ, _, rfl⟩; exact hτ φ)
  biact φ _ g' g := by rw [hτ, hτ, hb]
  compat φ hφ := by rw [hτ]; exact hc φ hφ

/-- **The tuple `(Λ, 𝒰', S', τ')`** (before Proposition 13.3.15) is structured. -/
def Tau.tight (t : D.Tau) (hΛ : IsScPlusMultisection A Λ) : (D.tight hΛ).Tau where
  τ := D.tightτ hΛ t
  isCorrespondence x x' := by
    have hsub : ∀ x, (D.tight hΛ).𝒰.U x ⊆ D.𝒰.U x := fun x => (D.tightNbhd_le x).subset
    -- the sections vanish at points `y` of `U(x)` with `Λ(0_y) = 1`
    have hzero : ∀ {z : A.Obj} (i : (D.S z).I) {y : A.Obj}, y ∈ D.𝒰.U z →
        Λ (fiberZero A.P y) = 1 → (D.S z).s i y = fiberZero A.P y :=
      fun i _ hy h1 => (D.S _).s_eq_fiberZero hΛ hy h1 i
    have hT : ∀ {z : A.Obj}, z ∈ trivialSet Λ → ∀ {y : A.Obj}, y ∈ (D.tight hΛ).𝒰.U z →
        Λ (fiberZero A.P y) = 1 :=
      fun hz _ hy => isTrivialOn_trivialSet Λ _ (D.tightNbhd_subset hz hy)
    by_cases hx : x ∈ trivialSet Λ <;> by_cases hx' : x' ∈ trivialSet Λ
    · refine isCorrespondence_const _ (tightτ_TT hx hx') (fun g' g => ?_) fun φ _ => ?_
      · exact (IndexCorr.biact_map g' g (TightIdx.eT hx) (TightIdx.eT hx') (Equiv.refl _)
          (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) _).trans
          (congrArg (fun c => IndexCorr.map (TightIdx.eT hx) (TightIdx.eT hx') c)
            (IndexCorr.map_refl _))
      · exact IndexCorr.sat_map (TightIdx.eT hx) (TightIdx.eT hx') (R := fun _ _ => True)
          (fun _ _ _ ψ _ => (fibAct_fiberZero rfl rfl).symm)
          (IndexCorr.sat_of_forall (fun _ _ => trivial) _)
    · refine isCorrespondence_const _ (tightτ_TN hx hx') (fun g' g => ?_) fun φ _ => ?_
      · exact (IndexCorr.biact_map g' g (TightIdx.eT hx) (TightIdx.eN hx') (Equiv.refl _)
          (MulAction.toPerm g') (fun _ => rfl) (fun _ => rfl) _).trans
          (congrArg (fun c => IndexCorr.map (TightIdx.eT hx) (TightIdx.eN hx') c)
            (@IndexCorr.map_toUnit_perm _ _ (D.nonempty_I hΛ x') _))
      · refine IndexCorr.sat_map (TightIdx.eT hx) (TightIdx.eN hx') (R := fun _ _ => True)
          (fun _ j _ ψ hψ => ?_) (IndexCorr.sat_of_forall (fun _ _ => trivial) _)
        have hψ' := (D.tight hΛ).𝒰.comp_subset x x' φ hψ
        change (D.S x').s j (A.X.tgt ψ) = fibAct ψ (fiberZero A.P (A.X.src ψ))
        rw [fibAct_fiberZero rfl rfl]
        exact hzero j (hsub x' hψ'.2) ((apply_fiberZero_tgt hΛ.1 ψ).trans (hT hx hψ'.1))
    · refine isCorrespondence_const _ (tightτ_NT hx hx') (fun g' g => ?_) fun φ _ => ?_
      · exact (IndexCorr.biact_map g' g (TightIdx.eN hx) (TightIdx.eT hx')
          (MulAction.toPerm g⁻¹) (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) _).trans
          (congrArg (fun c => IndexCorr.map (TightIdx.eN hx) (TightIdx.eT hx') c)
            (@IndexCorr.map_fromUnit_perm _ _ (D.nonempty_I hΛ x) _))
      · refine IndexCorr.sat_map (TightIdx.eN hx) (TightIdx.eT hx') (R := fun _ _ => True)
          (fun i _ _ ψ hψ => ?_) (IndexCorr.sat_of_forall (fun _ _ => trivial) _)
        have hψ' := (D.tight hΛ).𝒰.comp_subset x x' φ hψ
        change fiberZero A.P (A.X.tgt ψ) = fibAct ψ ((D.S x).s i (A.X.src ψ))
        rw [hzero i (hsub x hψ'.1) ((apply_fiberZero_tgt hΛ.1 ψ).symm.trans (hT hx' hψ'.2)),
          fibAct_fiberZero rfl rfl]
    · have hτ := fun φ => tightτ_NN (D := D) (hΛ := hΛ) (t := t) hx hx' φ
      have ht := t.isCorrespondence x x'
      have hmor := GoodSystem.mor_mono hsub x x'
      refine ⟨fun φ hφ => (ht.locallyConstant φ (hmor hφ)).mono fun ψ h =>
          (hτ ψ).trans ((congrArg _ h).trans (hτ φ).symm),
        (ht.finite.image fun c => c.map (TightIdx.eN hx) (TightIdx.eN hx')).subset ?_,
        fun φ hφ g' g => ?_, fun φ hφ => ?_⟩
      · rintro _ ⟨φ, hφ, rfl⟩
        exact ⟨t.τ x x' φ, mem_image_of_mem _ (hmor hφ), (hτ φ).symm⟩
      · rw [GoodSystem.biact_congr_of_le (fun z => D.tightNbhd_le z) hφ]
        refine (hτ _).trans ?_
        rw [ht.biact φ (hmor hφ)]
        refine Eq.trans ?_ (congrArg (fun c => IndexCorr.biact g' c g) (hτ φ)).symm
        exact (IndexCorr.biact_map g' g (TightIdx.eN hx) (TightIdx.eN hx')
          (MulAction.toPerm g⁻¹) (MulAction.toPerm g') (fun _ => rfl) (fun _ => rfl) _).symm
      · exact (congrArg (fun c => IndexCorr.Sat _ c) (hτ φ)).mpr
          (IndexCorr.sat_map _ _ (fun i j H ψ hψ =>
            H ψ (GoodSystem.comp_mono hsub x x' φ hψ)) (ht.compat φ (hmor hφ)))
  diag x g y hy := by
    by_cases hx : x ∈ trivialSet Λ
    · exact (tightτ_TT hx hx _).trans
        (IndexCorr.mk_eq_mk.2 ⟨TightIdx.eT hx, fun _ => ⟨rfl, rfl⟩⟩)
    · refine (tightτ_NN hx hx _).trans ?_
      change ((t.τ x x ((D.tightNbhd x).rep.Γ g y))).map _ _ = _
      rw [(D.tightNbhd_le x).Γ_eq g y hy, t.diag x g y ((D.tightNbhd_le x).subset hy)]
      exact IndexCorr.mk_eq_mk.2 ⟨TightIdx.eN hx, fun _ => ⟨rfl, rfl⟩⟩
  swap x x' φ hφ := by
    by_cases hx : x ∈ trivialSet Λ <;> by_cases hx' : x' ∈ trivialSet Λ
    · exact (tightτ_TT hx' hx φ).trans ((IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _,
        fun _ => ⟨rfl, rfl⟩⟩).trans (congrArg IndexCorr.swap (tightτ_TT hx hx' _)).symm)
    · exact (tightτ_NT hx' hx φ).trans ((IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _,
        fun _ => ⟨rfl, rfl⟩⟩).trans (congrArg IndexCorr.swap (tightτ_TN hx hx' _)).symm)
    · exact (tightτ_TN hx' hx φ).trans ((IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _,
        fun _ => ⟨rfl, rfl⟩⟩).trans (congrArg IndexCorr.swap (tightτ_NT hx hx' _)).symm)
    · refine (tightτ_NN hx' hx φ).trans (Eq.trans ?_
        (congrArg IndexCorr.swap (tightτ_NN hx hx' _)).symm)
      rw [t.swap x x' φ (GoodSystem.mor_mono (𝒲 := (D.tight hΛ).𝒰) (𝒰 := D.𝒰)
          (fun z => (D.tightNbhd_le z).subset) x' x hφ)]
      exact (IndexCorr.swap_map _ _ _).symm

/-! ### Definition 13.3.17 -/

/-- **2021 Definition 13.3.17, p. 620 (2017: Definition 13.21)**: `(Λ, 𝒰, S, τ)` is tight if
(1) for `x ∈ T_Λ`, `I_x = {∗}` and `sˣ` is the zero section; (2) for `x ∈ T_Λ`, `x' ∉ T_Λ`,
`τ_{x,x'}(φ) = [∗ ← I_{x'} →id I_{x'}]`, and for `x ∉ T_Λ`, `x' ∈ T_Λ`,
`τ_{x,x'}(φ) = [I_x ←id I_x → {∗}]`; (3) for `x, x' ∈ T_Λ`, `τ_{x,x'}(φ) = [{∗} ← {∗} → {∗}]`.
(`I_x = {∗}` is read as a bijection `{∗} ≃ I_x`; the conditions hold for every such bijection.) -/
structure IsTight (D : Decoration A Λ) (t : D.Tau) : Prop where
  unique : ∀ x ∈ trivialSet Λ, Nonempty (PUnit.{u + 1} ≃ (D.S x).I)
  zero : ∀ x ∈ trivialSet Λ, ∀ i, ∀ y ∈ D.𝒰.U x, (D.S x).s i y = fiberZero A.P y
  τ_TN : ∀ x ∈ trivialSet Λ, ∀ x' ∉ trivialSet Λ, ∀ φ ∈ D.𝒰.mor x x',
    ∀ (e : PUnit.{u + 1} ≃ (D.S x).I) [Nonempty (D.S x').I],
      t.τ x x' φ = (IndexCorr.toUnit (D.S x').I).map e (Equiv.refl _)
  τ_NT : ∀ x ∉ trivialSet Λ, ∀ x' ∈ trivialSet Λ, ∀ φ ∈ D.𝒰.mor x x',
    ∀ (e' : PUnit.{u + 1} ≃ (D.S x').I) [Nonempty (D.S x).I],
      t.τ x x' φ = (IndexCorr.fromUnit (D.S x).I).map (Equiv.refl _) e'
  τ_TT : ∀ x ∈ trivialSet Λ, ∀ x' ∈ trivialSet Λ, ∀ φ ∈ D.𝒰.mor x x',
    ∀ (e : PUnit.{u + 1} ≃ (D.S x).I) (e' : PUnit.{u + 1} ≃ (D.S x').I),
      t.τ x x' φ = (IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1})).map e e'

theorem isTight_tight (t : D.Tau) (hΛ : IsScPlusMultisection A Λ) :
    IsTight (D.tight hΛ) (t.tight hΛ) where
  unique x hx := ⟨TightIdx.eT hx⟩
  zero x hx := by
    intro κ y _
    change TightIdx _ _ at κ
    rcases κ with _ | ⟨_, h⟩
    · rfl
    · exact absurd hx h
  τ_TN x hx x' hx' φ _ e _ := by
    have := TightIdx.subsingleton (I := ((D.S x).restrict (D.tightNbhd_le x)).I) hx
    refine (tightτ_TN hx hx' φ).trans ?_
    exact IndexCorr.mk_eq_mk.2 ⟨TightIdx.eN hx', fun _ => ⟨Subsingleton.elim _ _, rfl⟩⟩
  τ_NT x hx x' hx' φ _ e' _ := by
    have := TightIdx.subsingleton (I := ((D.S x').restrict (D.tightNbhd_le x')).I) hx'
    refine (tightτ_NT hx hx' φ).trans ?_
    exact IndexCorr.mk_eq_mk.2 ⟨TightIdx.eN hx, fun _ => ⟨rfl, Subsingleton.elim _ _⟩⟩
  τ_TT x hx x' hx' φ _ e e' := by
    have := TightIdx.subsingleton (I := ((D.S x).restrict (D.tightNbhd_le x)).I) hx
    have := TightIdx.subsingleton (I := ((D.S x').restrict (D.tightNbhd_le x')).I) hx'
    refine (tightτ_TT hx hx' φ).trans ?_
    exact IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨Subsingleton.elim _ _,
      Subsingleton.elim _ _⟩⟩

end Decoration

/-- **Definition 13.3.17**: `[Λ, 𝒰, S, τ]` is tightly structured if some representative is
tight. -/
def StructuredMultisection.IsTight (L : StructuredMultisection A) : Prop :=
  ∃ T : StructuredTuple A, (Quotient.mk _ T : StructuredMultisection A) = L ∧
    Decoration.IsTight T.dec T.tau

/-! ### Proposition 13.3.15 and Corollary 13.3.18 -/

/-- **2021 Proposition 13.3.15, p. 619 (2017: Proposition 13.4)**: for a representative
`(Λ, 𝒰, S, τ)` there is a structured `(Λ, 𝒰', S', τ')` which is tight (items (1), (4), (5):
`Decoration.IsTight`), with `U'(x) ⊆ T_Λ` carrying the natural action of `U(x)` for `x ∈ T_Λ`
(item (1)), `U'(x) = U(x)` and `I'_x ≅ I_x` equivariantly with the same sections for `x ∉ T_Λ`
(item (2)), and `τ' = τ` (relabelled) for `x, x' ∉ T_Λ` (item (3)). -/
theorem proposition_13_3_15 {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (D : Decoration A Λ) (t : D.Tau) :
    ∃ (D' : Decoration A Λ) (t' : D'.Tau), D'.IsTight t' ∧
      (∀ x ∈ trivialSet Λ, D'.𝒰.U x ⊆ trivialSet Λ ∧ (D'.𝒰.nbhd x).Le (D.𝒰.nbhd x)) ∧
      ∃ e : ∀ x, x ∉ trivialSet Λ → ((D.S x).I ≃ (D'.S x).I),
        (∀ x (hx : x ∉ trivialSet Λ), D'.𝒰.nbhd x = D.𝒰.nbhd x ∧
          (∀ (g : A.X.Isotropy x) i, e x hx (g • i) = g • e x hx i) ∧
          ∀ i y, (D'.S x).s (e x hx i) y = (D.S x).s i y) ∧
        ∀ x x' (hx : x ∉ trivialSet Λ) (hx' : x' ∉ trivialSet Λ) φ,
          t'.τ x x' φ = (t.τ x x' φ).map (e x hx) (e x' hx') :=
  ⟨D.tight hΛ, t.tight hΛ, Decoration.isTight_tight t hΛ,
    fun x hx => ⟨D.tightNbhd_subset hx, D.tightNbhd_le x⟩,
    fun _ hx => TightIdx.eN hx,
    fun _ hx => ⟨D.tightNbhd_eq hx, fun _ _ => rfl, fun _ _ => rfl⟩,
    fun _ _ hx hx' φ => Decoration.tightτ_NN hx hx' φ⟩

/-- **2021 Corollary 13.3.18, p. 620 (2017: Corollary 13.1)**: every structurable `Λ` has a
tightly structured version. -/
theorem corollary_13_3_18 {Λ : A.W → ℚ≥0} (h : IsStructurable A Λ) :
    ∃ (D : Decoration A Λ) (t : D.Tau), D.IsTight t := by
  obtain ⟨hΛ, D, ⟨t⟩⟩ := h
  exact ⟨D.tight hΛ, t.tight hΛ, Decoration.isTight_tight t hΛ⟩

/-- **Corollary 13.3.18, for classes**: every `Λ ∈ Γ⁺_s(P)` is `forget` of a tightly structured
`[Λ, 𝒰, S, τ] ∈ Γ⁺_st(P)`. -/
theorem corollary_13_3_18_structured {Λ : A.W → ℚ≥0} (h : Λ ∈ Γs A) :
    ∃ L : Γst A, L.forget = Λ ∧ L.IsTight := by
  obtain ⟨hΛ, D, ⟨t⟩⟩ := h
  exact ⟨Quotient.mk _ ⟨⟨Λ, hΛ, D.tight hΛ⟩, t.tight hΛ⟩, rfl, _, rfl,
    Decoration.isTight_tight t hΛ⟩

end SBLocalization

end Polyfold
