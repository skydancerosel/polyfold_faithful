import Polyfold.Chapter1.FredholmIndex

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.1,
Definition 1.1.9 (preprint 1.8), Proposition 1.1.10 (preprint 1.9) and the proof of Proposition 1.1.11 (preprint 1.10) in Appendix §1.4.1, turned into
a criterion: **an sc-operator is sc-Fredholm iff it is Fredholm on level `0` and regularizing**,
and its consequence for restrictions to sc-subspaces (the sc form of Proposition 3.1.5 (preprint 3.5)'s direction
"`Dg(0)` sc-Fredholm ⟹ `Tf(0)` sc-Fredholm", used for Proposition 3.6.5 (preprint 3.52); round-trip items V3.46,
V3.68, V3.96; Findings, Chapter 3, items 233–234).

# A criterion for sc-Fredholm operators

## The text, paraphrased

(Definition 1.1.9 (preprint 1.8)) `T : E → F` is sc-Fredholm if there are sc-splittings `E = K ⊕ X`, `F = C ⊕ Y`
with `K = ker T` and `C` finite-dimensional, `Y = T(E)`, and `T : X → Y` an sc-isomorphism.
(Proposition 1.1.10 (preprint 1.9)) An sc-Fredholm operator is regularizing: `e ∈ E₀`, `T e ∈ F_m` imply `e ∈ E_m`.
(§1.4.1, proof of Proposition 1.1.11 (preprint 1.10)) For `T + S` the text builds the splittings from three facts
only: `T + S` is Fredholm, it is regularizing (`T` is, and `S` raises the level), and therefore its
kernel lies in `E_∞` and the smooth points of its range are dense on every level.

## What is formalized

* `Polyfold.ScOperator.IsRegularizing` (the conclusion of Proposition 1.1.10 (preprint 1.9) as a property),
  `ScOperator.IsRegularizing.ker_le_smooth` (the kernel of a regularizing operator is smooth),
  `ScOperator.IsRegularizing.surjective` (onto on level `0` ⟹ onto on every level),
  `Polyfold.IsScFredholm.isRegularizing` (Proposition 1.1.10 (preprint 1.9)).
* `Polyfold.isScFredholm_of_isRegularizing` (**the criterion**): an sc-operator that is Fredholm on
  level `0` and regularizing is sc-Fredholm (the construction of §1.4.1 with "regularizing" as the
  hypothesis); `Polyfold.isScFredholm_iff` (the converse is Proposition 1.1.10 (preprint 1.9) and Lemma 2.D);
  `Polyfold.isScFredholm_of_isRegularizing_index`: every level map is then Fredholm of the
  level-`0` index.
* `Polyfold.isScOperator_of_mapsTo` (**closed graph theorem**): a bounded `T₀ : E₀ → F₀` with
  `T₀(E_m) ⊆ F_m` for every `m` is an sc-operator (the continuity of `T₀ : E_m → F_m`, which
  Definition 1.1.4 (preprint 1.3) asks for, is automatic).
* `Polyfold.ScOperator.restrict`: the restriction `A → B` of an sc-operator `T : E → F` with
  `T(A) ⊆ B`, `A`, `B` sc-subspaces, as an sc-operator between the induced sc-Banach spaces
  (Definition 1.1.6 (preprint 1.5)); `ScOperator.IsRegularizing.restrict` (`A_m = A ∩ E_m`, so the restriction is
  regularizing when `T` is); `Polyfold.IsScFredholm.restrict` (**the restriction of an
  sc-Fredholm operator which is Fredholm on level `0` is sc-Fredholm**, with the level-`0` index on
  every level).

## What the text leaves implicit, and the choices made

* The criterion is not stated in the text; it is the proof of Proposition 1.1.11 (preprint 1.10) (§1.4.1) with the
  two properties it uses of `T + S` taken as hypotheses.  It is the tool for sc-Fredholmness of
  operators obtained from sc-Fredholm ones by conjugation and restriction (Propositions 3.1.5, 3.6.5 (preprint 3.5, 3.52),
  Theorem 3.1.22 (preprint 3.19)), for which the text says "is sc-Fredholm" without argument.
* The kernel hypothesis "`ker T ⊆ E_∞`" is not needed separately: it follows from regularizing.
* For the restriction to sc-subspaces only the Fredholm property **on level `0`** of the
  restriction is assumed; on the higher levels it follows (from the regularity of `T`), as does
  the sc-structure of the kernel and of a complement of the range.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### Regularizing sc-operators -/

namespace ScOperator

/-- An sc-operator `T : E → F` is **regularizing** (the property of Proposition 1.1.10 (preprint 1.9)): `e ∈ E₀` and
`T e ∈ F_m` imply `e ∈ E_m`. -/
def IsRegularizing (T : ScOperator E F) : Prop :=
  ∀ (m : ℕ) (e : E 0), T 0 e ∈ range (F.toBase m) → e ∈ range (E.toBase m)

/-- The kernel of a regularizing sc-operator consists of smooth points. -/
lemma IsRegularizing.ker_le_smooth {T : ScOperator E F} (h : T.IsRegularizing) :
    LinearMap.ker (T 0 : E 0 →ₗ[ℝ] F 0) ≤ E.smooth := by
  intro x hx
  rw [ScScale.mem_smooth_iff]
  intro m
  have hx0 : T 0 x = 0 := hx
  exact h m x (by rw [hx0]; exact ⟨0, map_zero _⟩)

/-- A regularizing sc-operator that is onto on level `0` is onto on every level. -/
lemma IsRegularizing.surjective {T : ScOperator E F} (h : T.IsRegularizing)
    (hs : Surjective (T 0)) (m : ℕ) : Surjective (T m) := by
  intro y
  obtain ⟨x, hx⟩ := hs (F.toBase m y)
  obtain ⟨x', rfl⟩ := h m x ⟨y, hx.symm⟩
  exact ⟨x', F.toBase_injective m (by rw [T.toBase_comm, hx])⟩

end ScOperator

/-- **Proposition 1.1.10 (preprint 1.9)**, as a property: an sc-Fredholm operator is regularizing. -/
theorem IsScFredholm.isRegularizing {T : ScOperator E F} (hT : IsScFredholm T) :
    T.IsRegularizing := by
  obtain ⟨s⟩ := hT
  exact fun _ _ he => proposition_1_1_10 s he

/-! ### The criterion -/

/-- **A criterion for sc-Fredholm operators** (the construction of §1.4.1): an sc-operator
`T : E → F` that is Fredholm on level `0` and regularizing is sc-Fredholm.  The kernel `K` is
finite-dimensional and smooth (regularizing), so it has an sc-complement (Proposition 1.1.7 (preprint 1.6)); the
range `Y` is closed, `Y_m = T(E_m)` (regularizing) and its smooth points are dense in `Y_m`
(images of smooth points); a complement `C` of `Y` spanned by smooth points exists because `F_∞`
is dense in `F₀` and `F₀/Y` is finite-dimensional. -/
theorem isScFredholm_of_isRegularizing {T : ScOperator E F} (hF : (T 0).IsFredholm)
    (hreg : T.IsRegularizing) : IsScFredholm T := by
  -- the kernel `K` is finite-dimensional and consists of smooth points
  set K := LinearMap.ker (T 0 : E 0 →ₗ[ℝ] F 0) with hK
  have hKfin : FiniteDimensional ℝ K := hF.finite_ker
  have hKsmooth : K ≤ E.smooth := hreg.ker_le_smooth
  obtain ⟨X, hX⟩ := E.proposition_1_1_7 K hKsmooth
  -- the range `Y` is closed and its smooth points are dense on every level
  set Y := LinearMap.range (T 0 : E 0 →ₗ[ℝ] F 0) with hY
  have hYcl : IsClosed (Y : Set (F 0)) := hF.isClosed_range
  have hYlvl : ∀ m, LinearMap.range (T m : E m →ₗ[ℝ] F m) = F.levelSub Y m := by
    intro m
    refine le_antisymm (T.range_lvl_le m) fun y hy => ?_
    rw [ScBanach.mem_levelSub] at hy
    obtain ⟨e, he⟩ := hy
    obtain ⟨e', rfl⟩ := hreg m e ⟨y, he.symm⟩
    refine ⟨e', F.toBase_injective m ?_⟩
    rw [ContinuousLinearMap.coe_coe, T.toBase_comm]
    exact he
  have hYsc : F.IsScSubspace Y := by
    refine ⟨hYcl, fun m y hy => ?_⟩
    rw [SetLike.mem_coe, ← hYlvl m] at hy
    obtain ⟨e, rfl⟩ := hy
    have hcl : e ∈ closure (E.smoothLvl m) := by
      rw [(E.dense_smooth m).closure_eq]; exact mem_univ _
    refine closure_mono ?_ (image_closure_subset_closure_image (T m).continuous ⟨e, hcl, rfl⟩)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨?_, T.mapsTo_smoothLvl m hz⟩
    rw [SetLike.mem_coe, ← hYlvl m]
    exact LinearMap.mem_range_self _ _
  -- the complement `C`: a right inverse of `F₀ → F₀/Y` with values in the smooth points
  have hQfin : FiniteDimensional ℝ (F 0 ⧸ Y) := hF.finite_coker
  set p := Y.mkQ with hp
  have hpsurj : LinearMap.range (p.domRestrict F.smooth) = ⊤ := by
    have hdense : Dense ((LinearMap.range (p.domRestrict F.smooth) : Submodule ℝ (F 0 ⧸ Y)) :
        Set (F 0 ⧸ Y)) := by
      have h1 : DenseRange Y.mkQL := (Submodule.mkQ_surjective _).denseRange
      have h2 : Dense (Y.mkQL '' (F.smooth : Set (F 0))) :=
        h1.dense_image Y.mkQL.continuous (by rw [← ScScale.smoothLvl_zero]; exact F.dense_smooth 0)
      refine h2.mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hcl : IsClosed ((LinearMap.range (p.domRestrict F.smooth) : Submodule ℝ (F 0 ⧸ Y)) :
        Set (F 0 ⧸ Y)) := Submodule.closed_of_finiteDimensional _
    rw [← Submodule.coe_eq_univ, ← hcl.closure_eq, hdense.closure_eq]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective (p.domRestrict F.smooth) hpsurj
  set σ : (F 0 ⧸ Y) →ₗ[ℝ] F 0 := F.smooth.subtype ∘ₗ g with hσ
  have hpσ : ∀ q, p (σ q) = q := fun q => by
    have := LinearMap.congr_fun hg q
    simpa [σ] using this
  set C := LinearMap.range σ with hC
  have hCsmooth : C ≤ F.smooth := by
    rintro _ ⟨q, rfl⟩
    exact (g q).2
  have hCfin : FiniteDimensional ℝ C := inferInstance
  -- `F_m = Y_m ⊕ C_m`
  have hcompl : ∀ m, IsCompl (F.levelSub Y m) (F.levelSub C m) := by
    intro m
    refine ⟨Submodule.disjoint_def.2 fun x hx hx' => ?_,
      Submodule.codisjoint_iff_exists_add_eq.2 fun z => ?_⟩
    · rw [ScBanach.mem_levelSub] at hx hx'
      obtain ⟨q, hq⟩ := hx'
      have h0 : (Submodule.Quotient.mk (F.toBase m x) : F 0 ⧸ Y) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hx
      have : q = 0 := by rw [← hpσ q, hq]; exact h0
      apply F.toBase_injective m
      rw [← hq, this, map_zero, map_zero]
    · obtain ⟨c, hc⟩ := (ScScale.mem_smooth_iff _).1 (hCsmooth (LinearMap.mem_range_self σ
        (Submodule.Quotient.mk (F.toBase m z)))) m
      refine ⟨z - c, c, ?_, ?_, sub_add_cancel z c⟩
      · rw [ScBanach.mem_levelSub, map_sub, hc, ← Submodule.Quotient.mk_eq_zero (p := Y),
          Submodule.Quotient.mk_sub]
        have : (Submodule.Quotient.mk (σ (Submodule.Quotient.mk (F.toBase m z))) : F 0 ⧸ Y) =
            Submodule.Quotient.mk (F.toBase m z) := hpσ _
        rw [this, sub_self]
      · rw [ScBanach.mem_levelSub, hc]
        exact LinearMap.mem_range_self σ _
  have hsplitF : F.IsScSplitting C Y :=
    ⟨(F.proposition_1_1_7_iff C).2 hCsmooth, hYsc, fun m => (hcompl m).symm⟩
  -- the bijections `X_m → Y_m`
  refine ⟨⟨K, X, C, Y, hX, hsplitF, rfl, hKfin, hCfin, rfl, fun m => ⟨?_, ?_, ?_⟩⟩⟩
  · intro x _
    rw [SetLike.mem_coe, ScBanach.mem_levelSub, T.toBase_comm]
    exact LinearMap.mem_range_self _ _
  · intro x hx x' hx' hxx'
    have hker : x - x' ∈ LinearMap.ker (T m : E m →ₗ[ℝ] F m) := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hxx', sub_self]
    rw [T.ker_lvl] at hker
    have hXm : x - x' ∈ E.levelSub X m := Submodule.sub_mem _ hx hx'
    have := (Submodule.disjoint_def.1 (hX.2.2 m).disjoint) _ hker hXm
    exact sub_eq_zero.1 this
  · intro y hy
    rw [← hYlvl m] at hy
    obtain ⟨e, rfl⟩ := hy
    obtain ⟨k, hk, x, hx, rfl⟩ := Submodule.mem_sup.1
      ((hX.2.2 m).sup_eq_top ▸ Submodule.mem_top (x := e))
    refine ⟨x, hx, ?_⟩
    have hk0 : T m k = 0 := by
      have : k ∈ LinearMap.ker (T m : E m →ₗ[ℝ] F m) := by rw [T.ker_lvl]; exact hk
      exact this
    rw [ContinuousLinearMap.coe_coe, map_add, hk0, zero_add]

/-- **The criterion, with the index**: an sc-operator that is Fredholm on level `0` and
regularizing is sc-Fredholm, and every level map `T_m : E_m → F_m` is Fredholm of the level-`0`
index (Lemma 2.D). -/
theorem isScFredholm_of_isRegularizing_index {T : ScOperator E F} (hF : (T 0).IsFredholm)
    (hreg : T.IsRegularizing) :
    IsScFredholm T ∧ ∀ m, (T m).IsFredholm ∧ fredholmIndex (T m) = fredholmIndex (T 0) := by
  have hT := isScFredholm_of_isRegularizing hF hreg
  exact ⟨hT, fun m => by rw [← scIndex_eq_fredholmIndex]; exact hT.fredholmIndex_lvl m⟩

/-- **Sc-Fredholm = Fredholm on level `0` + regularizing** (Proposition 1.1.10 (preprint 1.9) and the criterion). -/
theorem isScFredholm_iff {T : ScOperator E F} :
    IsScFredholm T ↔ (T 0).IsFredholm ∧ T.IsRegularizing := by
  refine ⟨fun hT => ⟨?_, hT.isRegularizing⟩, fun h => isScFredholm_of_isRegularizing h.1 h.2⟩
  obtain ⟨s⟩ := hT
  exact s.isFredholm 0

/-! ### Sc-operators from level-preserving bounded operators -/

/-- **A bounded operator `T₀ : E₀ → F₀` with `T₀(E_m) ⊆ F_m` for every `m` is an sc-operator**
(Definition 1.1.4 (preprint 1.3)): the continuity of `T₀ : E_m → F_m` follows from the closed graph theorem, since
`E_m → E₀` and `F_m → F₀` are continuous and injective. -/
theorem isScOperator_of_mapsTo {T₀ : E 0 →L[ℝ] F 0}
    (h : ∀ m (x : E m), T₀ (E.toBase m x) ∈ range (F.toBase m)) : IsScOperator T₀ := by
  intro m
  have h' : ∀ x : E m, ∃ y : F m, F.toBase m y = T₀ (E.toBase m x) := fun x => h m x
  choose g hg using h'
  have hadd : ∀ x y, g (x + y) = g x + g y := fun x y =>
    F.toBase_injective m (by rw [hg, map_add, map_add, map_add, hg, hg])
  have hsmul : ∀ (c : ℝ) x, g (c • x) = c • g x := fun c x =>
    F.toBase_injective m (by rw [hg, map_smul, map_smul, map_smul, hg])
  let gl : E m →ₗ[ℝ] F m := ⟨⟨g, hadd⟩, hsmul⟩
  have hcont : Continuous gl := gl.continuous_of_seq_closed_graph fun u x y hu hgu => by
    apply F.toBase_injective m
    change F.toBase m y = F.toBase m (g x)
    rw [hg]
    have h1 : Tendsto (fun n => F.toBase m (g (u n))) atTop (𝓝 (F.toBase m y)) :=
      ((F.toBase m).continuous.tendsto y).comp hgu
    have h2 : Tendsto (fun n => F.toBase m (g (u n))) atTop (𝓝 (T₀ (E.toBase m x))) := by
      simp_rw [hg]
      exact ((T₀.comp (E.toBase m)).continuous.tendsto x).comp hu
    exact tendsto_nhds_unique h1 h2
  exact ⟨⟨gl, hcont⟩, hg⟩

/-! ### Restriction to sc-subspaces -/

/-- For `x ∈ A` (level `0` of the induced sc-Banach space), `x ∈ A_m` iff `x ∈ E_m`. -/
lemma ScBanach.ofSubspace_mem_range_toBase_iff {A : Submodule ℝ (E 0)} (hA : E.IsScSubspace A)
    {m : ℕ} {x : (E.ofSubspace hA) 0} :
    x ∈ range ((E.ofSubspace hA).toBase m) ↔ (x.1 : E 0) ∈ range (E.toBase m) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, (E.ofSubspaceScale_coe_toBase hA.isClosed m y).symm⟩
  · rintro ⟨y, hy⟩
    have hyA : y ∈ E.levelSub A m := by
      rw [ScBanach.mem_levelSub, hy]; exact x.2
    exact ⟨⟨y, hyA⟩, Subtype.ext ((E.ofSubspaceScale_coe_toBase hA.isClosed m ⟨y, hyA⟩).trans hy)⟩

namespace ScOperator

variable (T : ScOperator E F) {A : Submodule ℝ (E 0)} {B : Submodule ℝ (F 0)}
  (hA : E.IsScSubspace A) (hB : F.IsScSubspace B) (hAB : ∀ x ∈ A, T 0 x ∈ B)

/-- The **restriction** `A → B` of an sc-operator `T : E → F` with `T(A) ⊆ B`, `A`, `B`
sc-subspaces, as an sc-operator between the induced sc-Banach spaces (level `m`:
`T_m : A_m → B_m`). -/
def restrict : ScOperator (E.ofSubspace hA) (F.ofSubspace hB) where
  lvl m := ((T m).comp (E.levelSub A m).subtypeL).codRestrict (F.levelSub B m) fun x => by
    rw [ScBanach.mem_levelSub, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      T.toBase_comm]
    exact hAB _ x.2
  incl_comm m x := Subtype.ext (T.incl_comm m x.1)

@[simp] lemma restrict_apply_coe (m : ℕ) (x : (E.ofSubspace hA) m) :
    ((T.restrict hA hB hAB m x).1 : F m) = T m x.1 := rfl

variable {T} in
/-- **The restriction of a regularizing sc-operator is regularizing** (`A_m = A ∩ E_m`). -/
theorem IsRegularizing.restrict (h : T.IsRegularizing) : (T.restrict hA hB hAB).IsRegularizing := by
  intro m x hx
  rw [ScBanach.ofSubspace_mem_range_toBase_iff] at hx ⊢
  exact h m x.1 hx

end ScOperator

variable {T : ScOperator E F} {A : Submodule ℝ (E 0)} {B : Submodule ℝ (F 0)}
  {hA : E.IsScSubspace A} {hB : F.IsScSubspace B} {hAB : ∀ x ∈ A, T 0 x ∈ B}

/-- **The restriction of a regularizing sc-operator to sc-subspaces is sc-Fredholm as soon as it is
Fredholm on level `0`**, and then Fredholm on every level with the level-`0` index. -/
theorem ScOperator.IsRegularizing.isScFredholm_restrict (h : T.IsRegularizing)
    (hF : (T.restrict hA hB hAB 0).IsFredholm) :
    IsScFredholm (T.restrict hA hB hAB) ∧ ∀ m, ((T.restrict hA hB hAB) m).IsFredholm ∧
      fredholmIndex ((T.restrict hA hB hAB) m) = fredholmIndex (T.restrict hA hB hAB 0) :=
  isScFredholm_of_isRegularizing_index hF (h.restrict hA hB hAB)

/-- **The restriction of an sc-Fredholm operator** `T : E → F` to sc-subspaces `A → B`
(`T(A) ⊆ B`) **is sc-Fredholm as soon as it is Fredholm on level `0`**, and then Fredholm on every
level with the level-`0` index.  (The sc form of Proposition 3.1.5 (preprint 3.5)'s direction "`Dg(0)` sc-Fredholm
⟹ `Tf(0)` sc-Fredholm", which needs the filler's condition (3) on level `0` only; round-trip items
V3.46, V3.68.) -/
theorem IsScFredholm.restrict (hT : IsScFredholm T) (hF : (T.restrict hA hB hAB 0).IsFredholm) :
    IsScFredholm (T.restrict hA hB hAB) ∧ ∀ m, ((T.restrict hA hB hAB) m).IsFredholm ∧
      fredholmIndex ((T.restrict hA hB hAB) m) = fredholmIndex (T.restrict hA hB hAB 0) :=
  hT.isRegularizing.isScFredholm_restrict hF

end Polyfold
