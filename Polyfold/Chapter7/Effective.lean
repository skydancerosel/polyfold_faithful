import Polyfold.Chapter7.NaturalAction
import Polyfold.Chapter7.NaturalRep
import Polyfold.Chapter7.Basic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §7.2,
pp. 239–241: the claim after **Definition 7.11** (p. 239), **Lemma 7.2** (p. 239), **Lemma 7.3**
(pp. 239–240), **Proposition 7.8** (pp. 240–241) and the discussion of `T_x` before
**Definition 7.12** (p. 241).  There is no 2014 preprint of Part II; numbers and pages are the
2017 text's.

# Effective ep-groupoids and the subgroup `T_x`

## The text, paraphrased

(Definition 7.11) `X` is effective if for every `x`, every `g ∈ G_x ∖ {1_x}` and every open
`𝐔(g)` there is `ψ ∈ 𝐔(g)` with `s(ψ) ≠ t(ψ)`; `x` is regular if `G_x = {1_x}`.  (p. 239) If
`s(φ)` is regular, so is `t(φ)`; `X_reg = {x | G_x = {1_x}}`.  (Lemma 7.2) `X_reg` is open: for
regular `x` and `U(x)` with the natural action, every `φ : a → b` between points of `U(x)` is
`Γ(1_x, a)`, so `b = a` and `φ = 1_a`.  "Examples show that the regular set can be empty."
(Lemma 7.3) Equivalent: (1) `X` is effective; (2) every open `V(x)` contains an open `U(x)` with
the natural action such that `Φ : G_x → Diff_sc(U(x))` is injective.  Proof of (1) ⇒ (2) by
contradiction: `Φ(h) = 1`, `h ≠ 1`; effectiveness gives `φ_k → h` with `s(φ_k) ≠ t(φ_k)`;
`φ_k = Γ(h_k, s(φ_k))` with `h_k ≠ h`, after a subsequence `h_k = g`; in the limit `h = Γ(g, x)`,
so `h = g`.  Proof of (2) ⇒ (1): `Φ(g) ≠ 1` gives `a` with `Φ(g)(a) ≠ a`, and `φ = Γ(g, a)` has
`s(φ) ≠ t(φ)`; "by taking smaller and smaller neighborhoods `U(x)` and adapting the corresponding
restrictions of `Γ`" one finds `φ_k → g`.  (Proposition 7.8) If `X` is effective, `X_reg` is
open and dense.  Proof: in `U(x₀)` take `x` with `#G_x` minimal; if `#G_x > 1`, Lemma 7.3 gives
`U(x) ⊆ U(x₀)` with `Φ` injective and, for `g ≠ 1`, a point `a` with `Φ(g)(a) ≠ a`; `G_a` is
isomorphic to `H = {h ∈ G_x | Φ(h)(a) = a}`, so `#G_x ≤ #G_a = #H ≤ #G_x`, `H = G_x`, a
contradiction.  (p. 241) `g ∈ G_x` acts trivially if `Φ(g) = 1` for some `U(x)` with the natural
action; since `G_x` is finite, `U(x)` can be chosen so small that the kernel of `Φ` is the
subgroup `T_x` of the elements acting trivially, a normal subgroup as a kernel.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **(p. 239)** `isRegular_tgt_of_isRegular_src` (from `GroupoidStr.isRegular_tgt_iff`);
  `isSaturated_regularSet`.
* **The kernel of `Φ`** for `R : X.NaturalRep x`: `NaturalRep.kerΦ` (the kernel of `G_x → Perm(U)`,
  `MulAction.toPermHom`), `NaturalRep.mem_kerΦ`, `NaturalRep.injective_Φ_iff`,
  `NaturalRep.kerΦ_eq_bot_iff`, `NaturalRep.kerΦ_eq_bot_iff_injective` (injectivity of `Φ` is
  "`Φ(g) = id` on `U` only for `g = 1`").
* **The isotropy of points of `U(x)`** (p. 241): `NaturalRep.stabilizerEquivIsotropy`
  (`{h ∈ G_x | Φ(h)(a) = a} ≅ G_a`, `h ↦ Γ(h, a)`), `NaturalRep.subset_regularSet`.
* **Lemma 7.2**: `lemma_7_2`.
* **Lemma 7.3**: `lemma_7_3`; (1) ⇒ (2) for *every* natural representation:
  `IsEffective.eq_one`, `isEffective_iff_forall_naturalRep`.
* **Proposition 7.8**: `proposition_7_8`; its converse (not in the text):
  `isEffective_of_dense_regularSet`, `isEffective_iff_dense_regularSet`.
* **`T_x`** (p. 241): `NaturalRep.actsTrivially_iff` (for every `R`: `g ∈ T_x` iff `Φ(g) = id` near
  `x`), `mem_trivialSet_of_section`, `mem_trivialSet_iff_eventually` (intrinsically: `g ∈ T_x` iff
  `s = t` near `g` in `𝐗`); "`T_x` is the kernel of `Φ` for small `U(x)`":
  `exists_mem_nhds_trivialSet_iff` (for *every* `R` inside a neighbourhood `N` of `x`),
  `exists_naturalRep_trivialSet_iff`, `exists_naturalRep_kerΦ_eq`; the subgroup
  `trivialSubgroup x` (carrier `trivialSet x`), `mem_trivialSubgroup`, `coe_trivialSubgroup`, the
  instance `trivialSubgroup_normal`; `normalClosure_trivialSet` and `effIsotropyEquiv`
  (`EffIsotropy x = G_x/T_x`); `NaturalRep.mem_trivialSet_of_val_eq_Γ` (`Γ(g, y) ∈ T_y`, used in
  the proof of Proposition 7.9, p. 242); **`T_x` along a morphism**: `isotropyConj_mem_trivialSet`,
  `isotropyConj_mem_trivialSet_iff`, `map_isotropyConj_trivialSubgroup` (`φ T_x φ⁻¹ = T_y`);
  `isEffective_iff_trivialSubgroup_eq_bot`.
* Satisfiability: `trivialSubgroup_trivial`.

## Reading

* **Lemma 7.2** uses `Γ(1_x, a) = 1_a`, which needs `U(x)` connected (`NaturalRep.Γ_one`,
  `NaturalAction.lean`; PLAN II.6, 3).  The lemma holds for *every* natural representation at a
  regular `x`: `NaturalRep.subset_regularSet`.  "Examples show that the regular set can be empty"
  is not formalized here (`ℤ/3 × ℝ ⇉ ℝ` with the trivial action, PLAN II.5, a W5 witness).
* **Lemma 7.3.**  "`Φ : G_x → Diff_sc(U(x))` is injective" is stated as `Φ(g) = id` on `U` only
  for `g = 1`; `NaturalRep.injective_Φ_iff` shows that this is the injectivity of
  `g ↦ Φ(g)|_U`, and `NaturalRep.kerΦ_eq_bot_iff`, `kerΦ_eq_bot_iff_injective` that it is the
  injectivity of the homomorphism `G_x → Perm(U)`.  Since `Diff_sc(U) ⊆ Perm(U)`, this is the
  injectivity into `Diff_sc(U)`.  (1) ⇒ (2) holds for
  **every** natural representation, not only small ones (`IsEffective.eq_one`): the sheet
  `Γ(h, U)` is itself an open neighbourhood of `h`, on which `s = t` if `Φ(h) = 1`; no sequence
  is needed.  In (2) ⇒ (1) the representations that (2) gives on smaller `U(x)` need not be
  restrictions of a first one, as we read the text's "adapting the corresponding restrictions of
  `Γ`"; they agree with it on the smaller `U(x)` by the uniqueness on connected sets
  (`NaturalRep.Γ_eqOn`), which is what the proof uses.  One application of (2) suffices: for a
  given open `𝐔(g)` we apply (2) to `V = {y ∈ U₀ | Γ₀(g, y) ∈ 𝐔(g)}`.
* **Proposition 7.8.**  The minimum of `#G_y` is taken over the given open set itself; the
  natural representation `U(x₀)` of the text is not needed.  Only "`#G_a = #H < #G_x`" is used,
  via `NaturalRep.stabilizerEquivIsotropy` (a group isomorphism, as the text says, though a
  bijection would do).  The converse (`isEffective_iff_dense_regularSet`) is not in the text: if
  `X_reg` is dense and `g ≠ 1`, a regular `a` near `x` with `Γ(g, a)` in a given `𝐔(g)` has
  `Γ(g, a) ≠ 1_a = Γ(1, a)`, so `s ≠ t` there.
* **`T_x` (p. 241).**  `T_x` is the union over all natural representations (Definition 7.12,
  `EpGroupoid.trivialSet`).  Since sc-smooth maps are not analytic, `Φ(g) = id` near `x` does not
  give `Φ(g) = id` on a connected `U(x)`; the kernel of `Φ` may depend on `U(x)`, which is why the
  text says "for small `U(x)`".  For example (not formalized: it needs a dimension-jumping
  retract), in the splicing example of PLAN II.6, 2 at `x = (−1, 0)` the natural representation on
  the whole connected `O` has trivial kernel while `T_x = ℤ/2`.  What holds is: for every `R`,
  `g ∈ T_x` iff `Φ(g) = id` near `x` (`NaturalRep.actsTrivially_iff`, through
  `eventually_Φ_eq_of_actsTrivially` and `exists_naturalRep_shrink`), and there is a neighbourhood
  `N` of `x` such that `ker Φ = T_x` for **every** natural representation with `U ⊆ N`
  (`exists_mem_nhds_trivialSet_iff`; `N` is the common fixed set in `U₀` of the elements of `T_x`
  for one `R₀`, a neighbourhood of `x` since `G_x` is finite, Proposition 7.4).  The text's
  "acting trivially on `U(x)`" is read so.  That `T_x` is a subgroup and normal is then the
  kernel argument of the text.  The text writes "`Φ : Gx → Diffsc (U(x)`" with a parenthesis
  missing (possible misprint).
* **`T_x` intrinsically** (not in the text): `g ∈ T_x` iff `s = t` on a neighbourhood of `g` in
  `𝐗` (`mem_trivialSet_iff_eventually`); so Definition 7.11 says exactly `T_x = {1_x}`
  (`isEffective_iff_trivialSubgroup_eq_bot`).
* **`T_x` at nearby points**: the proof of Proposition 7.9 (pp. 242–243) uses "`Γ(g, s(ψ'))`
  belongs to `T_{s(ψ')}`" for `g ∈ T_x = ker Φ`; this is `NaturalRep.mem_trivialSet_of_val_eq_Γ`.
* **`T_x` along a morphism** (not stated in the text; the composition of `X_R`, Proposition 7.10,
  needs `φ ∘ T_x = T_y ∘ φ`): for `φ : x → y` and `g ∈ T_x`, the
  map `z ↦ θ(z) ∘ Γ(g, s θ(z)) ∘ θ(z)⁻¹`, `θ = (t|𝐔(φ))⁻¹`, is a continuous section of `s` with
  `t = s` near `y` through `φ g φ⁻¹`; by `mem_trivialSet_of_section` (uniqueness of sections of
  `s` on connected sets) `φ g φ⁻¹ ∈ T_y`.  Its continuity uses condition (4) of Definition 7.3 in
  the sheet form (`isScSmoothCompSheet`), twice.
* **Hypotheses** (PLAN II.5, 5): `IsEffective` (Proposition 7.8, `IsEffective.eq_one`) holds for
  the trivial ep-groupoid (`isEffective_trivial`, vacuously: all `G_x` are trivial;
  `trivialSubgroup_trivial`).  A non-vacuous witness (`ℤ/2 ⋉ ℝ` by reflection) needs a finite
  group action as an ep-groupoid (`G × U` from `Discrete.lean`) and is not cheap here; it belongs
  to `NonVacuity.lean` (W5).  The "for every natural representation" of
  `isEffective_iff_forall_naturalRep` is equivalent to `IsEffective`, and natural representations
  exist (Theorem 7.1).  The hypotheses of `mem_trivialSet_of_section` are met by `k = Γ(g, ·)`
  (`NaturalRep.mem_trivialSet_of_val_eq_Γ`); "`X_reg` dense" by the trivial ep-groupoid
  (`regularSet_trivial`).  No hypothesis "for all charts" is added.
* No other possible misprint was found on pp. 239–241.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### The claim after Definition 7.11 -/

/-- **(p. 239)** "If `φ ∈ 𝐗` and `s(φ)` is a regular object, the same has to be true for
`t(φ)`." -/
theorem isRegular_tgt_of_isRegular_src {φ : Mor} (h : X.IsRegular (X.src φ)) :
    X.IsRegular (X.tgt φ) :=
  (X.isRegular_tgt_iff φ).2 h

/-- The regular part `X_reg` is saturated. -/
theorem isSaturated_regularSet : X.IsSaturated X.regularSet :=
  X.isSaturated_iff.2 fun _ h => X.isRegular_tgt_of_isRegular_src h

/-! ### The kernel of `Φ` and the isotropy of the points of `U(x)` -/

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-- For `U ⊆ U'`, the connected `U` lies in the component of `x` in `U ∩ U'`; so two natural
representations agree on the smaller `U` (uniqueness on connected sets, `NaturalAction.lean`). -/
private theorem subset_connectedComponentIn_inter {R' : X.NaturalRep x} (h : R.U ⊆ R'.U) :
    R.U ⊆ connectedComponentIn (R.U ∩ R'.U) x :=
  R.isConnected_U.isPreconnected.subset_connectedComponentIn R.mem_U (subset_inter subset_rfl h)

private theorem Γ_eqOn_of_subset {R' : X.NaturalRep x} (h : R.U ⊆ R'.U) (g : X.Isotropy x) :
    EqOn (R.Γ g) (R'.Γ g) R.U := fun _ hy =>
  R.Γ_eqOn R' g (R.subset_connectedComponentIn_inter h hy)

private theorem Φ_eqOn_of_subset {R' : X.NaturalRep x} (h : R.U ⊆ R'.U) (g : X.Isotropy x) :
    EqOn (R.Φ g) (R'.Φ g) R.U := fun _ hy =>
  R.Φ_eqOn R' g (R.subset_connectedComponentIn_inter h hy)

/-- **The kernel of `Φ`**: the kernel of `G_x → Perm(U)`, `g ↦ Φ(g)|_U`. -/
def kerΦ : Subgroup (X.Isotropy x) := (MulAction.toPermHom (X.Isotropy x) R.U).ker

theorem mem_kerΦ {g : X.Isotropy x} : g ∈ R.kerΦ ↔ ∀ y ∈ R.U, R.Φ g y = y := by
  rw [kerΦ, MonoidHom.mem_ker, Equiv.Perm.ext_iff]
  refine ⟨fun h y hy => congrArg Subtype.val (h ⟨y, hy⟩), fun h y => Subtype.ext (h y y.2)⟩

/-- **`Φ : G_x → Diff_sc(U)` is injective** iff `Φ(g) = id` on `U` only for `g = 1`. -/
theorem injective_Φ_iff :
    Injective (fun (g : X.Isotropy x) (y : R.U) => R.Φ g y) ↔
      ∀ g, (∀ y ∈ R.U, R.Φ g y = y) → g = 1 := by
  refine ⟨fun h g hg => h (funext fun y => ?_), fun h g g' he => ?_⟩
  · change R.Φ g y = R.Φ 1 y
    rw [hg y y.2, R.Φ_one y y.2]
  · refine inv_mul_eq_one.1 (h _ fun y hy => ?_)
    have hy' : R.Φ g y = R.Φ g' y := congrFun he ⟨y, hy⟩
    rw [R.Φ_mul _ _ y hy, ← hy', R.Φ_inv_Φ g hy]

theorem kerΦ_eq_bot_iff : R.kerΦ = ⊥ ↔ ∀ g, (∀ y ∈ R.U, R.Φ g y = y) → g = 1 := by
  simp only [Subgroup.eq_bot_iff_forall, R.mem_kerΦ]

/-- `g ↦ Φ(g)|_U` is injective iff `G_x → Perm(U)` is. -/
theorem kerΦ_eq_bot_iff_injective :
    R.kerΦ = ⊥ ↔ Injective (MulAction.toPermHom (X.Isotropy x) R.U) :=
  MonoidHom.ker_eq_bot_iff _

/-- **The isotropy of a point `a ∈ U(x)`** (p. 241): `{h ∈ G_x | Φ(h)(a) = a} ≅ G_a`,
`h ↦ Γ(h, a)`. -/
def stabilizerEquivIsotropy (a : R.U) :
    MulAction.stabilizer (X.Isotropy x) a ≃* X.Isotropy (a : Obj) where
  toFun h := ⟨R.Γ h.1 a, R.src_Γ _ _ a.2, (R.tgt_Γ _ _ a.2).trans
    (congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 h.2))⟩
  invFun k := ⟨R.index k.val, MulAction.mem_stabilizer_iff.2 (Subtype.ext (by
    have hk : k.val ∈ X.morOn R.U := ⟨by rw [k.src_val]; exact a.2, by rw [k.tgt_val]; exact a.2⟩
    have h := R.tgt_eq_Φ_index hk
    rw [k.src_val, k.tgt_val] at h
    exact h.symm))⟩
  left_inv h := Subtype.ext (R.index_Γ _ a.2)
  right_inv k := GroupoidStr.Isotropy.ext (by
    have hk : k.val ∈ X.morOn R.U := ⟨by rw [k.src_val]; exact a.2, by rw [k.tgt_val]; exact a.2⟩
    have h := R.Γ_index hk
    rw [k.src_val] at h
    exact h)
  map_mul' h h' := GroupoidStr.Isotropy.ext (by
    have hh' : R.Φ h'.1 a = a := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 h'.2)
    change R.Γ (h.1 * h'.1) a = X.comp (R.Γ h.1 a) (R.Γ h'.1 a)
    have hm := R.Γ_mul h.1 h'.1 a.2
    rw [hh'] at hm
    exact hm.symm)

/-- **Lemma 7.2, for every natural representation**: if `x` is regular, so is every point of
`U(x)`. -/
theorem subset_regularSet (hx : X.IsRegular x) : R.U ⊆ X.regularSet := fun a ha k => by
  obtain ⟨h, hh, -⟩ := R.existsUnique_Γ k.val (by rw [k.src_val]; exact ha)
    (by rw [k.tgt_val]; exact ha)
  rw [k.src_val, hx h, R.Γ_one ha] at hh
  exact GroupoidStr.Isotropy.ext hh.symm

end NaturalRep

/-! ### Lemma 7.2 -/

/-- **Lemma 7.2 (openness of the regular set)**: `X_reg` is open. -/
theorem lemma_7_2 : IsOpen X.regularSet := isOpen_iff_forall_mem_open.2 fun x hx => by
  obtain ⟨R, -⟩ := X.theorem_7_1 x isOpen_univ (mem_univ x)
  exact ⟨R.U, R.subset_regularSet hx, R.isOpen_U, R.mem_U⟩

/-! ### Lemma 7.3 -/

variable {X} in
/-- **Lemma 7.3, (1) ⇒ (2), for every natural representation**: if `X` is effective, `Φ(g) = id`
on `U` only for `g = 1`. -/
theorem IsEffective.eq_one (hX : X.IsEffective) {x : Obj} (R : X.NaturalRep x)
    {g : X.Isotropy x} (hg : ∀ y ∈ R.U, R.Φ g y = y) : g = 1 := by
  by_contra hne
  have hgW : g.val ∈ R.Γ g '' R.U := by
    have h := R.Γ_mem_image g R.mem_U
    rwa [R.Γ_self] at h
  obtain ⟨ψ, ⟨y, hy, rfl⟩, hψ⟩ := hX x g hne _ (R.isOpen_image_Γ g) hgW
  rw [R.src_Γ g y hy, R.tgt_Γ g y hy, hg y hy] at hψ
  exact hψ rfl

/-- **Lemma 7.3**: `X` is effective iff (2) every open `V ∋ x` contains the `U` of a natural
representation of `G_x` with `Φ : G_x → Diff_sc(U)` injective. -/
theorem lemma_7_3 : X.IsEffective ↔ ∀ x, ∀ V : Set Obj, IsOpen V → x ∈ V →
    ∃ R : X.NaturalRep x, R.U ⊆ V ∧ ∀ g, (∀ y ∈ R.U, R.Φ g y = y) → g = 1 := by
  refine ⟨fun h x V hV hx => (X.theorem_7_1 x hV hx).imp fun R hR => ⟨hR, fun _ => h.eq_one R⟩,
    fun h x g hg W hW hgW => ?_⟩
  obtain ⟨R₀, -⟩ := X.theorem_7_1 x isOpen_univ (mem_univ x)
  have hUo : IsOpen (R₀.U ∩ R₀.Γ g ⁻¹' W) :=
    (R₀.continuousOn_Γ g).isOpen_inter_preimage R₀.isOpen_U hW
  have hxU : x ∈ R₀.U ∩ R₀.Γ g ⁻¹' W := ⟨R₀.mem_U, by rw [mem_preimage, R₀.Γ_self]; exact hgW⟩
  obtain ⟨R, hRU, hinj⟩ := h x _ hUo hxU
  have hnot : ¬ ∀ y ∈ R.U, R.Φ g y = y := fun h' => hg (hinj g h')
  push Not at hnot
  obtain ⟨a, ha, hga⟩ := hnot
  have hΓ : R.Γ g a = R₀.Γ g a :=
    NaturalRep.Γ_eqOn_of_subset R (fun y hy => (hRU hy).1) g ha
  refine ⟨R.Γ g a, by rw [hΓ]; exact (hRU ha).2, ?_⟩
  rw [R.src_Γ g a ha, R.tgt_Γ g a ha]
  exact Ne.symm hga

/-- **Lemma 7.3 for every natural representation**: `X` is effective iff `Φ` is injective for
every natural representation. -/
theorem isEffective_iff_forall_naturalRep : X.IsEffective ↔
    ∀ x (R : X.NaturalRep x) g, (∀ y ∈ R.U, R.Φ g y = y) → g = 1 :=
  ⟨fun h _ R _ => h.eq_one R, fun h => X.lemma_7_3.2 fun x _ hV hx =>
    (X.theorem_7_1 x hV hx).imp fun R hR => ⟨hR, h x R⟩⟩

/-! ### Proposition 7.8 -/

/-- **Proposition 7.8**: if `X` is effective, `X_reg` is open and dense. -/
theorem proposition_7_8 (hX : X.IsEffective) : IsOpen X.regularSet ∧ Dense X.regularSet := by
  refine ⟨X.lemma_7_2, dense_iff_inter_open.2 fun O hO hne => ?_⟩
  -- `x ∈ O` with `#G_x` minimal (7.3)
  let f : Obj → ℕ := fun y => Nat.card (X.Isotropy y)
  have hxO : argminOn f O hne ∈ O := argminOn_mem f O hne
  refine ⟨argminOn f O hne, hxO, fun g => ?_⟩
  by_contra hg
  obtain ⟨R, hRO⟩ := X.theorem_7_1 _ hO hxO
  have hnot : ¬ ∀ y ∈ R.U, R.Φ g y = y := fun h => hg (hX.eq_one R h)
  push Not at hnot
  obtain ⟨a, ha, hga⟩ := hnot
  let a' : R.U := ⟨a, ha⟩
  -- `#G_a = #H < #G_x`
  have hlt : Nat.card (MulAction.stabilizer (X.Isotropy (argminOn f O hne)) a') <
      Nat.card (X.Isotropy (argminOn f O hne)) := by
    refine lt_of_le_of_ne (Subgroup.card_le_card_group _) fun he => hga ?_
    have hmem : g ∈ MulAction.stabilizer (X.Isotropy (argminOn f O hne)) a' := by
      rw [(Subgroup.card_eq_iff_eq_top _).1 he]
      exact Subgroup.mem_top g
    exact congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hmem)
  rw [Nat.card_congr (R.stabilizerEquivIsotropy a').toEquiv] at hlt
  exact not_lt_argminOn f O (hRO ha) hlt

/-- **The converse of Proposition 7.8** (not in the text): if `X_reg` is dense, `X` is
effective. -/
theorem isEffective_of_dense_regularSet (h : Dense X.regularSet) : X.IsEffective := by
  intro x g hg W hW hgW
  obtain ⟨R, -⟩ := X.theorem_7_1 x isOpen_univ (mem_univ x)
  obtain ⟨a, ⟨ha, haW⟩, hreg⟩ := dense_iff_inter_open.1 h _
    ((R.continuousOn_Γ g).isOpen_inter_preimage R.isOpen_U hW)
    ⟨x, R.mem_U, by rw [mem_preimage, R.Γ_self]; exact hgW⟩
  refine ⟨R.Γ g a, haW, fun he => hg ?_⟩
  have hs := R.src_Γ g a ha
  have hv : R.Γ g a = X.unit a :=
    congrArg GroupoidStr.Isotropy.val (hreg ⟨R.Γ g a, hs, he.symm.trans hs⟩)
  rw [← R.Γ_one ha] at hv
  exact (R.Γ_inj ha).1 hv

/-- **An ep-groupoid is effective iff its regular part is dense.** -/
theorem isEffective_iff_dense_regularSet : X.IsEffective ↔ Dense X.regularSet :=
  ⟨fun h => (X.proposition_7_8 h).2, X.isEffective_of_dense_regularSet⟩

/-! ### `T_x`: germs of the natural action -/

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-- **`T_x` seen by one natural representation**: `g` acts trivially iff `Φ(g) = id` near `x`,
for every natural representation `R`. -/
theorem actsTrivially_iff {g : X.Isotropy x} :
    X.ActsTrivially g ↔ ∀ᶠ y in 𝓝 x, R.Φ g y = y := by
  refine ⟨R.eventually_Φ_eq_of_actsTrivially, fun h => ?_⟩
  obtain ⟨N, hN, hNo, hxN⟩ := mem_nhds_iff.1 h
  obtain ⟨R', hR'U, hR'Φ, -⟩ := X.exists_naturalRep_shrink R hNo hxN
  exact ⟨R', fun y hy => by rw [hR'Φ]; exact hN (hR'U hy).1⟩

end NaturalRep

/-- **A criterion for `T_y`**: `h ∈ G_y` acts trivially if `h` lies on a continuous section `k`
of `s` over an open `D ∋ y` with `t ∘ k = id` on `D`. -/
theorem mem_trivialSet_of_section {y : Obj} {h : X.Isotropy y} {D : Set Obj} (hD : IsOpen D)
    (hyD : y ∈ D) {k : Obj → Mor} (hk : ContinuousOn k D) (hks : ∀ z ∈ D, X.src (k z) = z)
    (hkt : ∀ z ∈ D, X.tgt (k z) = z) (hky : k y = h.val) : h ∈ X.trivialSet y := by
  obtain ⟨R, -⟩ := X.theorem_7_1 y isOpen_univ (mem_univ y)
  refine R.actsTrivially_iff.2 ?_
  have hyC : y ∈ connectedComponentIn (D ∩ R.U) y := mem_connectedComponentIn ⟨hyD, R.mem_U⟩
  have hC := connectedComponentIn_subset (D ∩ R.U) y
  have heq : EqOn k (R.Γ h) (connectedComponentIn (D ∩ R.U) y) :=
    eqOn_sections_of_isPreconnected X.isLocalScDiffeo_src.isLocallyInjective
      isPreconnected_connectedComponentIn (hk.mono fun z hz => (hC hz).1)
      ((R.continuousOn_Γ h).mono fun z hz => (hC hz).2) (fun z hz => hks z (hC hz).1)
      (fun z hz => R.src_Γ h z (hC hz).2) hyC (by rw [hky, R.Γ_self])
  filter_upwards [(X.PObj.isOpen_connectedComponentIn (hD.inter R.isOpen_U) y).mem_nhds hyC]
    with z hz
  rw [← R.tgt_Γ h z (hC hz).2, ← heq hz]
  exact hkt z (hC hz).1

/-- **`T_x` intrinsically** (not in the text): `g ∈ T_x` iff `s = t` on a neighbourhood of `g` in
`𝐗`. -/
theorem mem_trivialSet_iff_eventually {x : Obj} {g : X.Isotropy x} :
    g ∈ X.trivialSet x ↔ ∀ᶠ ψ in 𝓝 g.val, X.src ψ = X.tgt ψ := by
  constructor
  · rintro ⟨R, hR⟩
    have hgW : g.val ∈ R.Γ g '' R.U := by
      have h := R.Γ_mem_image g R.mem_U
      rwa [R.Γ_self] at h
    filter_upwards [(R.isOpen_image_Γ g).mem_nhds hgW] with ψ hψ
    obtain ⟨y, hy, rfl⟩ := hψ
    rw [R.src_Γ g y hy, R.tgt_Γ g y hy, hR y hy]
  · intro h
    obtain ⟨W₁, V₁, σ, hgW₁, hd⟩ := X.isLocalScDiffeo_src g.val
    have hσg : σ x = g.val := by
      have h' := hd.left_inv _ hgW₁
      rwa [g.src_val] at h'
    have hxV₁ : x ∈ V₁ := by
      have h' := hd.mapsTo hgW₁
      rwa [g.src_val] at h'
    refine X.mem_trivialSet_of_section
      (hd.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hd.isOpen_target isOpen_interior)
      ⟨hxV₁, by rw [mem_preimage, hσg]; exact mem_interior_iff_mem_nhds.2 h⟩
      (hd.isScSmoothOn_inv.continuousOn.mono inter_subset_left)
      (fun z hz => hd.right_inv z hz.1) (fun z hz => ?_) hσg
    rw [← interior_subset hz.2, hd.right_inv z hz.1]

/-! ### `T_x` is the kernel of `Φ` for small `U(x)` -/

/-- **"`T_x` is the kernel of `Φ` for small `U(x)`"** (p. 241), for every small natural
representation: there is a neighbourhood `N` of `x` such that `ker Φ = T_x` for every natural
representation with `U ⊆ N`. -/
theorem exists_mem_nhds_trivialSet_iff (x : Obj) :
    ∃ N ∈ 𝓝 x, ∀ R : X.NaturalRep x, R.U ⊆ N →
      ∀ g, g ∈ X.trivialSet x ↔ ∀ y ∈ R.U, R.Φ g y = y := by
  obtain ⟨R₀, -⟩ := X.theorem_7_1 x isOpen_univ (mem_univ x)
  have hev : ∀ᶠ y in 𝓝 x, ∀ g, g ∈ X.trivialSet x → R₀.Φ g y = y := by
    refine Filter.eventually_all.2 fun g => ?_
    by_cases hg : g ∈ X.trivialSet x
    · filter_upwards [R₀.eventually_Φ_eq_of_actsTrivially hg] with y hy _ using hy
    · exact Filter.Eventually.of_forall fun _ h => absurd h hg
  refine ⟨{y | ∀ g, g ∈ X.trivialSet x → R₀.Φ g y = y} ∩ R₀.U,
    inter_mem hev (R₀.isOpen_U.mem_nhds R₀.mem_U), fun R hRN g => ⟨fun hg y hy => ?_,
    fun h => ⟨R, h⟩⟩⟩
  rw [NaturalRep.Φ_eqOn_of_subset R (fun z hz => (hRN hz).2) g hy]
  exact (hRN hy).1 g hg

/-- **`T_x` is the kernel of `Φ` for small `U(x)`** (p. 241): every open `V ∋ x` contains the `U`
of a natural representation with `ker Φ = T_x`. -/
theorem exists_naturalRep_trivialSet_iff (x : Obj) {V : Set Obj} (hV : IsOpen V) (hx : x ∈ V) :
    ∃ R : X.NaturalRep x, R.U ⊆ V ∧ ∀ g, g ∈ X.trivialSet x ↔ ∀ y ∈ R.U, R.Φ g y = y := by
  obtain ⟨N, hN, hNR⟩ := X.exists_mem_nhds_trivialSet_iff x
  obtain ⟨R, hRU⟩ := X.theorem_7_1 x (isOpen_interior.inter hV)
    ⟨mem_interior_iff_mem_nhds.2 hN, hx⟩
  exact ⟨R, fun y hy => (hRU hy).2, hNR R fun y hy => interior_subset (hRU hy).1⟩

/-! ### `T_x` as a normal subgroup -/

/-- **`T_x` as a subgroup of `G_x`** (p. 241), with carrier `trivialSet x`. -/
def trivialSubgroup (x : Obj) : Subgroup (X.Isotropy x) where
  carrier := X.trivialSet x
  mul_mem' {g h} hg hh := by
    obtain ⟨R, -, hR⟩ := X.exists_naturalRep_trivialSet_iff x isOpen_univ (mem_univ x)
    exact ⟨R, fun y hy => by rw [R.Φ_mul g h y hy, (hR h).1 hh y hy, (hR g).1 hg y hy]⟩
  one_mem' := by
    obtain ⟨R, -⟩ := X.theorem_7_1 x isOpen_univ (mem_univ x)
    exact X.one_mem_trivialSet R
  inv_mem' {g} hg := by
    obtain ⟨R, hR⟩ := hg
    exact ⟨R, fun y hy => (congrArg (R.Φ g⁻¹) (hR y hy)).symm.trans (R.Φ_inv_Φ g hy)⟩

theorem mem_trivialSubgroup {x : Obj} {g : X.Isotropy x} :
    g ∈ X.trivialSubgroup x ↔ g ∈ X.trivialSet x :=
  Iff.rfl

@[simp]
theorem coe_trivialSubgroup (x : Obj) : (X.trivialSubgroup x : Set (X.Isotropy x)) =
    X.trivialSet x :=
  rfl

/-- **`T_x` is a normal subgroup** of `G_x` (p. 241). -/
instance trivialSubgroup_normal (x : Obj) : (X.trivialSubgroup x).Normal where
  conj_mem n hn g := by
    obtain ⟨R, hR⟩ := hn
    refine ⟨R, fun y hy => ?_⟩
    have hy' := R.mapsTo_Φ g⁻¹ hy
    rw [R.Φ_mul _ _ y hy, R.Φ_mul _ _ _ hy', hR _ hy', R.Φ_Φ_inv g hy]

/-- **`T_x` is the kernel of `Φ` for small `U(x)`**, as subgroups. -/
theorem exists_naturalRep_kerΦ_eq (x : Obj) {V : Set Obj} (hV : IsOpen V) (hx : x ∈ V) :
    ∃ R : X.NaturalRep x, R.U ⊆ V ∧ R.kerΦ = X.trivialSubgroup x := by
  obtain ⟨R, hRV, hR⟩ := X.exists_naturalRep_trivialSet_iff x hV hx
  exact ⟨R, hRV, Subgroup.ext fun g => R.mem_kerΦ.trans (hR g).symm⟩

/-- The normal closure of `T_x` is `T_x`. -/
theorem normalClosure_trivialSet (x : Obj) :
    Subgroup.normalClosure (X.trivialSet x) = X.trivialSubgroup x :=
  Subgroup.normalClosure_eq_self (X.trivialSubgroup x)

/-- **Definition 7.13**: `EffIsotropy x = G_x ⧸ normalClosure(T_x)` is `G_x/T_x`. -/
def effIsotropyEquiv (x : Obj) : X.EffIsotropy x ≃* X.Isotropy x ⧸ X.trivialSubgroup x :=
  QuotientGroup.quotientMulEquivOfEq (X.normalClosure_trivialSet x)

/-- **`X` is effective iff every `T_x` is trivial.** -/
theorem isEffective_iff_trivialSubgroup_eq_bot :
    X.IsEffective ↔ ∀ x, X.trivialSubgroup x = ⊥ := by
  refine ⟨fun h x => (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_, fun h =>
    X.isEffective_iff_forall_naturalRep.2 fun x R g hg =>
      (Subgroup.eq_bot_iff_forall _).1 (h x) g ⟨R, hg⟩⟩
  obtain ⟨R, hR⟩ := hg
  exact h.eq_one R hR

/-! ### `T_x` at nearby points and along morphisms -/

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-- **`Γ(g, y) ∈ T_y`** for `g` acting trivially on `U` and `y ∈ U` (used in the proof of
Proposition 7.9, p. 242: "the morphism `Γ(g, s(ψ'))` belongs to `T_{s(ψ')}`"). -/
theorem mem_trivialSet_of_val_eq_Γ {g : X.Isotropy x} (hg : ∀ z ∈ R.U, R.Φ g z = z) {y : Obj}
    (hy : y ∈ R.U) {h : X.Isotropy y} (hh : h.val = R.Γ g y) : h ∈ X.trivialSet y :=
  X.mem_trivialSet_of_section R.isOpen_U hy (R.continuousOn_Γ g) (R.src_Γ g)
    (fun z hz => (R.tgt_Γ g z hz).trans (hg z hz)) hh.symm

end NaturalRep

/-- The section `z ↦ θ(z) ∘ Γ(g, s θ(z)) ∘ θ(z)⁻¹` of `s` near `y`, `θ = (t|𝐔(φ))⁻¹`, through
`φ g φ⁻¹`, for `φ : x → y` and `g` acting trivially on `U(x)`. -/
private theorem exists_conj_section {x y : Obj} {φ : Mor} (hx : X.src φ = x) (hy : X.tgt φ = y)
    (R : X.NaturalRep x) {g : X.Isotropy x} (hR : ∀ z ∈ R.U, R.Φ g z = z) :
    ∃ D : Set Obj, IsOpen D ∧ y ∈ D ∧ ∃ k : Obj → Mor, ContinuousOn k D ∧
      (∀ z ∈ D, X.src (k z) = z) ∧ (∀ z ∈ D, X.tgt (k z) = z) ∧
      k y = X.comp (X.comp φ g.val) (X.inv φ) := by
  have hθ := (X.sheetAt φ).isScDiffeoOn_tgt
  have hσ := (X.sheetAt φ).isScDiffeoOn_src
  set S := X.sheetAt φ
  set D := S.tgtSet ∩ (fun z => X.src (S.tgtInv z)) ⁻¹' R.U
  have hDo : IsOpen D := (X.continuous_src.comp_continuousOn
    hθ.isScSmoothOn_inv.continuousOn).isOpen_inter_preimage hθ.isOpen_target R.isOpen_U
  have hφy : S.tgtInv y = φ := by rw [← hy]; exact hθ.left_inv φ (X.mem_sheetAt φ)
  have hyD : y ∈ D := ⟨hy ▸ X.tgt_mem_sheetAt φ, by
    rw [mem_preimage, hφy, hx]; exact R.mem_U⟩
  -- the inner morphism `Γ(g, w) ∘ θ(z)⁻¹ : z → w`, `w = s θ(z)`
  have hc₁ : ∀ z ∈ D, X.src (R.Γ g (X.src (S.tgtInv z))) = X.tgt (X.inv (S.tgtInv z)) :=
    fun z hz => by rw [R.src_Γ g _ hz.2, X.tgt_inv]
  have hit : ∀ z ∈ D, X.tgt (X.comp (R.Γ g (X.src (S.tgtInv z))) (X.inv (S.tgtInv z))) =
      X.src (S.tgtInv z) := fun z hz => by
    rw [X.tgt_comp _ _ (hc₁ z hz), R.tgt_Γ g _ hz.2, hR _ hz.2]
  have his : ∀ z ∈ D, X.src (X.comp (R.Γ g (X.src (S.tgtInv z))) (X.inv (S.tgtInv z))) = z :=
    fun z hz => by rw [X.src_comp _ _ (hc₁ z hz), X.src_inv, hθ.right_inv z hz.1]
  refine ⟨D, hDo, hyD, fun z => X.comp (S.tgtInv z)
    (X.comp (R.Γ g (X.src (S.tgtInv z))) (X.inv (S.tgtInv z))), ?_, fun z hz => ?_,
    fun z hz => ?_, ?_⟩
  · -- continuity, from Definition 7.3 (4) in the sheet form, twice
    have hF₁ := (R.isScSmoothOn_comp_Γ_tgt g).continuousOn
    have hF₂ := (X.isScSmoothCompSheet S.srcInv S.carrier S.srcSet hσ).continuousOn
    have hψ : ContinuousOn (fun z => X.inv (S.tgtInv z)) D :=
      X.continuous_inv.comp_continuousOn (hθ.isScSmoothOn_inv.continuousOn.mono inter_subset_left)
    have h₁ : MapsTo (fun z => X.inv (S.tgtInv z)) D (X.tgt ⁻¹' R.U) := fun z hz => by
      rw [mem_preimage, X.tgt_inv]; exact hz.2
    have h₂ : MapsTo ((fun ψ => X.comp (R.Γ g (X.tgt ψ)) ψ) ∘ fun z => X.inv (S.tgtInv z)) D
        (X.tgt ⁻¹' S.srcSet) := fun z hz => by
      rw [mem_preimage, Function.comp_apply, X.tgt_inv, hit z hz]
      exact hσ.mapsTo (hθ.mapsTo_inv hz.1)
    refine (hF₂.comp (hF₁.comp hψ h₁) h₂).congr fun z hz => ?_
    simp only [Function.comp_apply, X.tgt_inv, hit z hz, hσ.left_inv _ (hθ.mapsTo_inv hz.1)]
  · rw [X.src_comp _ _ (hit z hz).symm, his z hz]
  · rw [X.tgt_comp _ _ (hit z hz).symm, hθ.right_inv z hz.1]
  · simp only [hφy, hx, R.Γ_self]
    exact (X.comp_assoc _ _ _ (by rw [hx, g.tgt_val]) (by rw [g.src_val, X.tgt_inv, hx])).symm

/-- **`T_x` along a morphism**: for `φ : x → y` and `g ∈ T_x`, `φ g φ⁻¹ ∈ T_y`. -/
theorem isotropyConj_mem_trivialSet {x y : Obj} (φ : Mor) (hx : X.src φ = x) (hy : X.tgt φ = y)
    {g : X.Isotropy x} (hg : g ∈ X.trivialSet x) : X.isotropyConj φ hx hy g ∈ X.trivialSet y := by
  obtain ⟨R, hR⟩ := hg
  obtain ⟨D, hDo, hyD, k, hk, hks, hkt, hky⟩ := X.exists_conj_section hx hy R hR
  exact X.mem_trivialSet_of_section hDo hyD hk hks hkt hky

theorem isotropyConj_mem_trivialSet_iff {x y : Obj} (φ : Mor) (hx : X.src φ = x)
    (hy : X.tgt φ = y) (g : X.Isotropy x) :
    X.isotropyConj φ hx hy g ∈ X.trivialSet y ↔ g ∈ X.trivialSet x := by
  refine ⟨fun h => ?_, X.isotropyConj_mem_trivialSet φ hx hy⟩
  have hx' : X.src (X.inv φ) = y := (X.src_inv φ).trans hy
  have hy' : X.tgt (X.inv φ) = x := (X.tgt_inv φ).trans hx
  have h' := X.isotropyConj_mem_trivialSet (X.inv φ) hx' hy' h
  have hc : X.src g.val = X.tgt (X.inv φ) := by rw [g.src_val, hy']
  have he : X.isotropyConj (X.inv φ) hx' hy' (X.isotropyConj φ hx hy g) = g := by
    refine GroupoidStr.Isotropy.ext ?_
    simp only [GroupoidStr.isotropyConj_val]
    rw [X.comp_assoc _ _ _ (by rw [hx, g.tgt_val]) hc,
      GroupoidStr.inv_comp_cancel_left (by rw [X.tgt_comp _ _ hc, g.tgt_val, hx]),
      GroupoidStr.comp_inv_cancel_right hc]
  rw [he] at h'
  exact h'

/-- **`φ T_x φ⁻¹ = T_y`** for `φ : x → y`. -/
theorem map_isotropyConj_trivialSubgroup {x y : Obj} (φ : Mor) (hx : X.src φ = x)
    (hy : X.tgt φ = y) :
    (X.trivialSubgroup x).map (X.isotropyConj φ hx hy).toMonoidHom = X.trivialSubgroup y := by
  ext h
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact X.isotropyConj_mem_trivialSet φ hx hy hg
  · intro hh
    refine ⟨(X.isotropyConj φ hx hy).symm h, (X.isotropyConj_mem_trivialSet_iff φ hx hy _).1 ?_,
      MulEquiv.apply_symm_apply _ _⟩
    rw [MulEquiv.apply_symm_apply]
    exact hh

/-! ### Satisfiability -/

/-- In the trivial ep-groupoid, `T_x` is trivial (as is `G_x`; it is effective,
`isEffective_trivial`). -/
theorem trivialSubgroup_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) (x : Z) : (trivial P).trivialSubgroup x = ⊥ :=
  Subgroup.eq_bot_of_subsingleton _

end EpGroupoid

end Polyfold
