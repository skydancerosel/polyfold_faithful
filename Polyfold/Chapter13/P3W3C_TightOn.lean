import Polyfold.Chapter13.P3W3C_PiCorrespondence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.3, the step of the proof of **Proposition 13.3.19** (p. 620; 2017: Proposition 13.5) that
passes to tight versions "using the same `𝒰`".

# Tight versions relative to a given good system

Proposition 13.3.15 shrinks `U(x)` into `T_Λ` at the points of `T_Λ`.  The proof of
Proposition 13.3.19 needs the tight version over one good system `𝒰` shared by all members of a
family.  This is possible when `𝒰` is *adapted* to `(Λ, 𝒰_Λ, S, τ)`: `U(x) ⊆ T_Λ` for `x ∈ T_Λ`,
and `U(x)` lies in `U_Λ(x)` with the same action for `x ∉ T_Λ` (`Decoration.IsAdapted`).

* `SymmetricStructureOn.tightRel`: the structure on `I'_x = {∗}` (zero section) for `x ∈ T_Λ`,
  `I'_x = I_x` (restricted sections) for `x ∉ T_Λ`, on the neighbourhood of `𝒰`.
* `Decoration.tightOn`, `Decoration.tightOnτ` (the correspondences: the given `τ` between points
  outside `T_Λ`, the unit diagrams otherwise), `Decoration.Tau.tightOn` (a structure on `𝒰`), and
  `Decoration.isTight_tightOn` (it is tight, Definition 13.3.17).
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

namespace SymmetricStructureOn

variable {Λ : A.W → ℚ≥0} {x : A.Obj}

/-- **The tight structure on another neighbourhood** `N`: the zero section on `∗` where `p`
(then `Λ` is trivial on `N`), the sections of `S` on `I_x` where `¬p` (then `N ≤ N₁`). -/
def tightRel {N₁ : A.X.NatNbhd x} (S : SymmetricStructureOn A Λ N₁)
    (hΛ : IsScPlusMultisection A Λ) (N : A.X.NatNbhd x) (p : Prop) (hp : p → IsTrivialOn Λ N.U)
    (hle : ¬p → N.Le N₁) : SymmetricStructureOn A Λ N where
  I := TightIdx p S.I
  s := Sum.elim (fun _ => fiberZero A.P) fun i : {_i : S.I // ¬p} => S.s i.1
  isScPlusSectionOn := by
    rintro (_ | i)
    · exact isScPlusSectionOn_fiberZero N.isOpen_U
    · exact (S.isScPlusSectionOn i.1).mono N.isOpen_U (hle i.2).subset
  equivariant g κ y hy := by
    rcases κ with _ | i
    · exact (fibAct_fiberZero (N.src_Γ g hy) (N.tgt_Γ g hy)).symm
    · have h := hle i.2
      have e := S.equivariant g i.1 y (h.subset hy)
      rw [← h.Φ_eq g hy, ← h.Γ_eq g y hy] at e
      exact e
  rep w hw := by
    by_cases hp' : p
    · rw [(ofTrivial hΛ (hp hp')).rep w hw]
      refine (count_reindex (TightIdx.eT hp').symm (fun κ => ?_) w).symm
      rcases κ with _ | ⟨_, h⟩
      · rfl
      · exact absurd hp' h
    · rw [S.rep w ((hle hp').subset hw)]
      refine (count_reindex (TightIdx.eN hp').symm (fun κ => ?_) w).symm
      rcases κ with ⟨_, h⟩ | _
      · exact absurd h hp'
      · rfl

end SymmetricStructureOn

namespace Decoration

variable {Λ : A.W → ℚ≥0}

/-- **A good system adapted to a decoration** (properties (3)–(4) in the proof of Proposition
13.3.19): `U(x) ⊆ T_Λ` for `x ∈ T_Λ`, and `U(x) ≤ U_Λ(x)` (same action) for `x ∉ T_Λ`. -/
structure IsAdapted (D : Decoration A Λ) (𝒰 : A.X.GoodSystem) : Prop where
  triv : ∀ x ∈ trivialSet Λ, 𝒰.U x ⊆ trivialSet Λ
  le : ∀ x ∉ trivialSet Λ, (𝒰.nbhd x).Le (D.𝒰.nbhd x)

/-- **The tight version of `(𝒰_Λ, S)` on an adapted good system `𝒰`.** -/
def tightOn (D : Decoration A Λ) (hΛ : IsScPlusMultisection A Λ) (𝒰 : A.X.GoodSystem)
    (h : D.IsAdapted 𝒰) : Decoration A Λ :=
  ⟨𝒰, fun x => (D.S x).tightRel hΛ (𝒰.nbhd x) (x ∈ trivialSet Λ)
    (fun hx y hy => isTrivialOn_trivialSet Λ y (h.triv x hx hy)) (h.le x)⟩

variable {D : Decoration A Λ} {hΛ : IsScPlusMultisection A Λ} {𝒰 : A.X.GoodSystem}
  {h : D.IsAdapted 𝒰}

/-- **The correspondences of the tight version on `𝒰`.** -/
def tightOnτ (D : Decoration A Λ) (hΛ : IsScPlusMultisection A Λ) (𝒰 : A.X.GoodSystem)
    (h : D.IsAdapted 𝒰) (t : D.Tau) (x x' : A.Obj) (φ : A.Mor) :
    IndexCorr ((D.tightOn hΛ 𝒰 h).S x).I ((D.tightOn hΛ 𝒰 h).S x').I :=
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

variable {t : D.Tau} {x x' : A.Obj}

theorem tightOnτ_TT (hx : x ∈ trivialSet Λ) (hx' : x' ∈ trivialSet Λ) (φ : A.Mor) :
    D.tightOnτ hΛ 𝒰 h t x x' φ =
      (IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1})).map (TightIdx.eT hx) (TightIdx.eT hx') := by
  rw [tightOnτ, dif_pos hx, dif_pos hx']
  rfl

theorem tightOnτ_TN (hx : x ∈ trivialSet Λ) (hx' : x' ∉ trivialSet Λ) (φ : A.Mor) :
    D.tightOnτ hΛ 𝒰 h t x x' φ = (@IndexCorr.toUnit (D.S x').I _ (D.nonempty_I hΛ x')).map
      (TightIdx.eT hx) (TightIdx.eN hx') := by
  rw [tightOnτ, dif_pos hx, dif_neg hx']
  rfl

theorem tightOnτ_NT (hx : x ∉ trivialSet Λ) (hx' : x' ∈ trivialSet Λ) (φ : A.Mor) :
    D.tightOnτ hΛ 𝒰 h t x x' φ = (@IndexCorr.fromUnit (D.S x).I _ (D.nonempty_I hΛ x)).map
      (TightIdx.eN hx) (TightIdx.eT hx') := by
  rw [tightOnτ, dif_neg hx, dif_pos hx']
  rfl

theorem tightOnτ_NN (hx : x ∉ trivialSet Λ) (hx' : x' ∉ trivialSet Λ) (φ : A.Mor) :
    D.tightOnτ hΛ 𝒰 h t x x' φ = (t.τ x x' φ).map (TightIdx.eN hx) (TightIdx.eN hx') := by
  rw [tightOnτ, dif_neg hx, dif_neg hx']
  rfl

/-- **The tight version on an adapted `𝒰` is structured** (proof of Proposition 13.3.19, "we can
pass, following Proposition 13.3.15, … to a tightly structured version using the same `𝒰`"). -/
def Tau.tightOn (t : D.Tau) (hΛ : IsScPlusMultisection A Λ) (𝒰 : A.X.GoodSystem)
    (h : D.IsAdapted 𝒰) : (D.tightOn hΛ 𝒰 h).Tau where
  τ := D.tightOnτ hΛ 𝒰 h t
  isCorrespondence x x' := by
    have hzero : ∀ {z : A.Obj} (i : (D.S z).I) {y : A.Obj}, y ∈ D.𝒰.U z →
        Λ (fiberZero A.P y) = 1 → (D.S z).s i y = fiberZero A.P y :=
      fun i _ hy h1 => (D.S _).s_eq_fiberZero hΛ hy h1 i
    have hT : ∀ {z : A.Obj}, z ∈ trivialSet Λ → ∀ {y : A.Obj}, y ∈ 𝒰.U z →
        Λ (fiberZero A.P y) = 1 :=
      fun hz _ hy => isTrivialOn_trivialSet Λ _ (h.triv _ hz hy)
    by_cases hx : x ∈ trivialSet Λ <;> by_cases hx' : x' ∈ trivialSet Λ
    · refine isCorrespondence_const _ (tightOnτ_TT hx hx') (fun g' g => ?_) fun φ _ => ?_
      · exact (IndexCorr.biact_map g' g (TightIdx.eT hx) (TightIdx.eT hx') (Equiv.refl _)
          (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) _).trans
          (congrArg (fun c => IndexCorr.map (TightIdx.eT hx) (TightIdx.eT hx') c)
            (IndexCorr.map_refl _))
      · exact IndexCorr.sat_map (TightIdx.eT hx) (TightIdx.eT hx') (R := fun _ _ => True)
          (fun _ _ _ ψ _ => (fibAct_fiberZero rfl rfl).symm)
          (IndexCorr.sat_of_forall (fun _ _ => trivial) _)
    · refine isCorrespondence_const _ (tightOnτ_TN hx hx') (fun g' g => ?_) fun φ _ => ?_
      · exact (IndexCorr.biact_map g' g (TightIdx.eT hx) (TightIdx.eN hx') (Equiv.refl _)
          (MulAction.toPerm g') (fun _ => rfl) (fun _ => rfl) _).trans
          (congrArg (fun c => IndexCorr.map (TightIdx.eT hx) (TightIdx.eN hx') c)
            (@IndexCorr.map_toUnit_perm _ _ (D.nonempty_I hΛ x') _))
      · refine IndexCorr.sat_map (TightIdx.eT hx) (TightIdx.eN hx') (R := fun _ _ => True)
          (fun _ j _ ψ hψ => ?_) (IndexCorr.sat_of_forall (fun _ _ => trivial) _)
        have hψ' := 𝒰.comp_subset x x' φ hψ
        change (D.S x').s j (A.X.tgt ψ) = fibAct ψ (fiberZero A.P (A.X.src ψ))
        rw [fibAct_fiberZero rfl rfl]
        exact hzero j ((h.le x' hx').subset hψ'.2)
          ((apply_fiberZero_tgt hΛ.1 ψ).trans (hT hx hψ'.1))
    · refine isCorrespondence_const _ (tightOnτ_NT hx hx') (fun g' g => ?_) fun φ _ => ?_
      · exact (IndexCorr.biact_map g' g (TightIdx.eN hx) (TightIdx.eT hx')
          (MulAction.toPerm g⁻¹) (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) _).trans
          (congrArg (fun c => IndexCorr.map (TightIdx.eN hx) (TightIdx.eT hx') c)
            (@IndexCorr.map_fromUnit_perm _ _ (D.nonempty_I hΛ x) _))
      · refine IndexCorr.sat_map (TightIdx.eN hx) (TightIdx.eT hx') (R := fun _ _ => True)
          (fun i _ _ ψ hψ => ?_) (IndexCorr.sat_of_forall (fun _ _ => trivial) _)
        have hψ' := 𝒰.comp_subset x x' φ hψ
        change fiberZero A.P (A.X.tgt ψ) = fibAct ψ ((D.S x).s i (A.X.src ψ))
        rw [hzero i ((h.le x hx).subset hψ'.1)
            ((apply_fiberZero_tgt hΛ.1 ψ).symm.trans (hT hx' hψ'.2)),
          fibAct_fiberZero rfl rfl]
    · have hτ := fun φ => tightOnτ_NN (D := D) (hΛ := hΛ) (𝒰 := 𝒰) (h := h) (t := t) hx hx' φ
      have ht := t.isCorrespondence x x'
      have hmor : 𝒰.mor x x' ⊆ D.𝒰.mor x x' :=
        morBetween_mono (h.le x hx).subset (h.le x' hx').subset
      refine ⟨fun φ hφ => (ht.locallyConstant φ (hmor hφ)).mono fun ψ h =>
          (hτ ψ).trans ((congrArg _ h).trans (hτ φ).symm),
        (ht.finite.image fun c => c.map (TightIdx.eN hx) (TightIdx.eN hx')).subset ?_,
        fun φ hφ g' g => ?_, fun φ hφ => ?_⟩
      · rintro _ ⟨φ, hφ, rfl⟩
        exact ⟨t.τ x x' φ, mem_image_of_mem _ (hmor hφ), (hτ φ).symm⟩
      · have hb : (D.tightOn hΛ 𝒰 h).𝒰.biact x x' g' φ g = D.𝒰.biact x x' g' φ g :=
          EpGroupoid.biact_congr_of_le (h.le x hx) (h.le x' hx') hφ g' g
        rw [hb]
        refine (hτ _).trans ?_
        rw [ht.biact φ (hmor hφ)]
        refine Eq.trans ?_ (congrArg (fun c => IndexCorr.biact g' c g) (hτ φ)).symm
        exact (IndexCorr.biact_map g' g (TightIdx.eN hx) (TightIdx.eN hx')
          (MulAction.toPerm g⁻¹) (MulAction.toPerm g') (fun _ => rfl) (fun _ => rfl) _).symm
      · exact (congrArg (fun c => IndexCorr.Sat _ c) (hτ φ)).mpr
          (IndexCorr.sat_map _ _ (fun i j H ψ hψ =>
            H ψ (connectedComponentIn_mono φ hmor hψ)) (ht.compat φ (hmor hφ)))
  diag x g y hy := by
    by_cases hx : x ∈ trivialSet Λ
    · exact (tightOnτ_TT hx hx _).trans
        (IndexCorr.mk_eq_mk.2 ⟨TightIdx.eT hx, fun _ => ⟨rfl, rfl⟩⟩)
    · refine (tightOnτ_NN hx hx _).trans ?_
      change ((t.τ x x ((𝒰.nbhd x).rep.Γ g y))).map _ _ = _
      rw [(h.le x hx).Γ_eq g y hy, t.diag x g y ((h.le x hx).subset hy)]
      exact IndexCorr.mk_eq_mk.2 ⟨TightIdx.eN hx, fun _ => ⟨rfl, rfl⟩⟩
  swap x x' φ hφ := by
    by_cases hx : x ∈ trivialSet Λ <;> by_cases hx' : x' ∈ trivialSet Λ
    · exact (tightOnτ_TT hx' hx φ).trans ((IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _,
        fun _ => ⟨rfl, rfl⟩⟩).trans (congrArg IndexCorr.swap (tightOnτ_TT hx hx' _)).symm)
    · exact (tightOnτ_NT hx' hx φ).trans ((IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _,
        fun _ => ⟨rfl, rfl⟩⟩).trans (congrArg IndexCorr.swap (tightOnτ_TN hx hx' _)).symm)
    · exact (tightOnτ_TN hx' hx φ).trans ((IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _,
        fun _ => ⟨rfl, rfl⟩⟩).trans (congrArg IndexCorr.swap (tightOnτ_NT hx hx' _)).symm)
    · refine (tightOnτ_NN hx' hx φ).trans (Eq.trans ?_
        (congrArg IndexCorr.swap (tightOnτ_NN hx hx' _)).symm)
      rw [t.swap x x' φ (morBetween_mono (h.le x' hx').subset (h.le x hx).subset hφ)]
      exact (IndexCorr.swap_map _ _ _).symm

/-- **The tight version on an adapted `𝒰` is tight** (Definition 13.3.17). -/
theorem isTight_tightOn (t : D.Tau) (hΛ : IsScPlusMultisection A Λ) (𝒰 : A.X.GoodSystem)
    (h : D.IsAdapted 𝒰) : IsTight (D.tightOn hΛ 𝒰 h) (t.tightOn hΛ 𝒰 h) where
  unique x hx := ⟨TightIdx.eT hx⟩
  zero x hx := by
    intro κ y _
    change TightIdx _ _ at κ
    rcases κ with _ | ⟨_, h⟩
    · rfl
    · exact absurd hx h
  τ_TN x hx x' hx' φ _ e _ := by
    have := TightIdx.subsingleton (I := (D.S x).I) hx
    refine (tightOnτ_TN hx hx' φ).trans ?_
    exact IndexCorr.mk_eq_mk.2 ⟨TightIdx.eN hx', fun _ => ⟨Subsingleton.elim _ _, rfl⟩⟩
  τ_NT x hx x' hx' φ _ e' _ := by
    have := TightIdx.subsingleton (I := (D.S x').I) hx'
    refine (tightOnτ_NT hx hx' φ).trans ?_
    exact IndexCorr.mk_eq_mk.2 ⟨TightIdx.eN hx, fun _ => ⟨rfl, Subsingleton.elim _ _⟩⟩
  τ_TT x hx x' hx' φ _ e e' := by
    have := TightIdx.subsingleton (I := (D.S x).I) hx
    have := TightIdx.subsingleton (I := (D.S x').I) hx'
    refine (tightOnτ_TT hx hx' φ).trans ?_
    exact IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨Subsingleton.elim _ _,
      Subsingleton.elim _ _⟩⟩

end Decoration

end SBLocalization

end Polyfold
