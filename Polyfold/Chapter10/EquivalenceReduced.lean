import Polyfold.Chapter10.Equivalence
import Polyfold.Chapter7.Zhou

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.1 "Equivalences", pp. 472–476: **Remark 10.1.12, Propositions 10.1.13,
10.1.14, 10.1.16, 10.1.18** (Proposition 10.1.14 is 2017: Proposition 10.5, p. 341; the others
are new in the 2021 edition).  Numbers and pages are the 2021 text's.

# Equivalences, the non-effective part and the reduced ep-groupoid

## The text, paraphrased

(Remark 10.1.12, p. 472) For an equivalence `F` and `ψ : F(x) → y`, `F : G_x → G_{F(x)}` and
`σ ↦ ψ ∘ σ ∘ ψ⁻¹` are group isomorphisms mapping `T_x` onto `T_{F(x)}` and `T_{F(x)}` onto
`T_y`; so `ψ` gives an isomorphism `G_x → G_y` mapping `T_x` onto `T_y`.  (Proposition 10.1.13,
p. 472) For an equivalence `F`, (1) `F_R : 𝐗^R → 𝐘^R` is continuous and open, (2) the natural
topology `T_R` of one of them is Hausdorff iff the other's is.  *Proof* (text): `F_R` is a local
homeomorphism; for (2), by the criterion "`T_R` Hausdorff iff `𝐗^T` closed", a conjugation
`G(γ)` by local inverses of `s` shows `𝐗^T` closed ⇒ `𝐘^T` closed, and the converse is direct.
(Proposition 10.1.14, p. 473 (2017: Proposition 10.5, p. 341)) If `F` is an equivalence and
`𝐗^R`, `𝐘^R` are Hausdorff, `F_R = F` on objects and `F_R[φ] = [F(φ)]` is a well-defined functor
`X_R → Y_R` and an equivalence.  (Proposition 10.1.16, p. 474) (LUC) passes along equivalences
(both directions).  *Proof* (text): (LUC) iff `𝐗^T` closed, and a sequence argument as in 10.1.13.
(Proposition 10.1.18, p. 476) (SLUC) passes along equivalences.  *Proof* (text): the lifts
`Fⁱ : Xⁱ → Yⁱ` are equivalences, and (LUC) passes along each.

## What is formalized

* `EpFunctor.mor_mem_nonEffectivePart`, `mem_nonEffectivePart_of_mor`, `nonEffectivePart_eq`
  (`𝐗^T = F⁻¹(𝐘^T) ∩ {s = t}` for `F` a local sc-diffeomorphism on objects);
  `EpFunctor.isotropyHom` (`G_x → G_{F(x)}`), `isotropyHom_mem_trivialSet_iff`,
  `IsEquivalence.bijective_isotropyHom`; `IsEquivalence.remark_10_1_12` (**Remark 10.1.12**).
* `IsEquivalence.isClosed_nonEffectivePart_iff` (`𝐗^T` closed iff `𝐘^T` closed);
  `EpFunctor.proposition_10_1_16` (**Proposition 10.1.16**).
* `EpFunctor.reducedMap` (`F_R`), `continuous_reducedMap`, `isOpenMap_reducedMap`;
  `EpFunctor.proposition_10_1_13` (**Proposition 10.1.13**).
* `EpFunctor.reducedGroupoidFunctor`, `EpFunctor.reduced` (`F_R : X_R → Y_R`),
  `EpFunctor.proposition_10_1_14` (**Proposition 10.1.14**).
* `EpFunctor.liftOne` (`F¹ : X¹ → Y¹`), `IsEquivalence.liftOne`,
  `EP.exists_isEquivalence_lift`; `EP.proposition_10_1_18` (**Proposition 10.1.18**).

## What the text leaves implicit, and the choices made

* "`T_R` Hausdorff iff `𝐗^T` closed" and "(LUC) iff `𝐗^T` closed" are the existing
  `proposition_7_2_17` and `proposition_7_2_21`; the proofs of 10.1.13 and 10.1.16
  cite them through Theorem 7.2.22 (p. 323), which collects them.  The proof of Proposition 10.1.18 cites Proposition 10.1.9 for the step (LUC) along
  `Fⁱ`, which is Proposition 10.1.16 (possible misprint).  Remark 10.1.12 ends with `G_x → Y_y`
  for `G_x → G_y` (possible misprint).
* `𝐗^T` closed ⇒ `𝐘^T` closed is proved with closures and the conjugation
  `χ ↦ b(t χ)⁻¹ ∘ χ ∘ b(s χ)` (`b` a local inverse of `t` at `σ : F(x) → y`), in place of the
  text's sequences and properness.
* Proposition 10.1.13 (1) is stated for `F` an equivalence; `reducedMap` only needs a local
  sc-diffeomorphism on objects.  Proposition 10.1.14 keeps the text's hypothesis that both
  reduced spaces are Hausdorff (by 10.1.13 (2) one of them would suffice); `X_R` is the existing
  `reducedEpGroupoid`.
* (SLUC) is the existing `EP.IsSLUC` (Definition 7.4.12) on the bundled `EP`; the lifts are
  Chapter 7's `EP.lift`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v w

section Reduced

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

namespace EpFunctor

variable (F : EpFunctor X Y) (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj)
include hF

/-! ### The non-effective parts under a local sc-diffeomorphism on objects -/

/-- **`F(𝐗^T) ⊆ 𝐘^T`** for a functor which is a local sc-diffeomorphism on objects: near `φ`,
`F` on morphisms is a local homeomorphism, and `s = t` near `φ` gives `s = t` near `F(φ)`. -/
theorem mor_mem_nonEffectivePart {φ : Mor} (hφ : φ ∈ X.nonEffectivePart) :
    F.mor φ ∈ Y.nonEffectivePart := by
  rw [X.mem_nonEffectivePart_iff] at hφ
  rw [Y.mem_nonEffectivePart_iff]
  obtain ⟨U, V, g, hφU, hd⟩ := F.isLocalScDiffeoAt_mor (hF.at (X.src φ))
  have hmap : map F.mor (𝓝 φ) = 𝓝 (F.mor φ) := hd.toOpenPartialHomeomorph.map_nhds_eq hφU
  rw [← hmap, eventually_map]
  filter_upwards [hφ] with ψ hψ
  rw [F.src_mor, F.tgt_mor, hψ]

/-- **The converse on `{s = t}`**: if `s(φ) = t(φ)` and `F(φ) ∈ 𝐘^T`, then `φ ∈ 𝐗^T` (`F` is
injective near `s(φ) = t(φ)`). -/
theorem mem_nonEffectivePart_of_mor {φ : Mor} (hst : X.src φ = X.tgt φ)
    (h : F.mor φ ∈ Y.nonEffectivePart) : φ ∈ X.nonEffectivePart := by
  rw [X.mem_nonEffectivePart_iff]
  have h1 : ∀ᶠ ψ in 𝓝 φ, F.obj (X.src ψ) = F.obj (X.tgt ψ) := by
    filter_upwards [(F.continuous_mor.tendsto φ).eventually (Y.mem_nonEffectivePart_iff.1 h)]
      with ψ hψ
    rwa [F.src_mor, F.tgt_mor] at hψ
  obtain ⟨U, V, g, hxU, hd⟩ := hF (X.src φ)
  have hs : ∀ᶠ ψ in 𝓝 φ, X.src ψ ∈ U :=
    (X.continuous_src.tendsto φ).eventually (hd.isOpen_source.mem_nhds hxU)
  have ht : ∀ᶠ ψ in 𝓝 φ, X.tgt ψ ∈ U :=
    (X.continuous_tgt.tendsto φ).eventually (hd.isOpen_source.mem_nhds (by rw [← hst]; exact hxU))
  filter_upwards [h1, hs, ht] with ψ h1 hs ht
  exact hd.injOn hs ht h1

/-- `𝐗^T = F⁻¹(𝐘^T) ∩ {s = t}`. -/
theorem nonEffectivePart_eq :
    X.nonEffectivePart = F.mor ⁻¹' Y.nonEffectivePart ∩ {φ | X.src φ = X.tgt φ} :=
  Set.ext fun _ => ⟨fun h => ⟨F.mor_mem_nonEffectivePart hF h,
    EpGroupoid.src_eq_tgt_of_mem_nonEffectivePart h⟩,
    fun h => F.mem_nonEffectivePart_of_mor hF h.2 h.1⟩

omit hF in
/-- The isotropy homomorphism `G_x → G_{F(x)}`, `g ↦ F(g)`. -/
def isotropyHom (x : Obj) : X.Isotropy x →* Y.Isotropy (F.obj x) where
  toFun g := ⟨F.mor g.val, by rw [F.src_mor, g.src_val], by rw [F.tgt_mor, g.tgt_val]⟩
  map_one' := GroupoidStr.Isotropy.ext (F.mor_unit x)
  map_mul' g h := GroupoidStr.Isotropy.ext (F.mor_comp _ _ (g.src_val.trans h.tgt_val.symm))

omit hF in
@[simp]
theorem isotropyHom_val (x : Obj) (g : X.Isotropy x) : (F.isotropyHom x g).val = F.mor g.val :=
  rfl

/-- `F : G_x → G_{F(x)}` maps `T_x` onto `T_{F(x)}`: `g ∈ T_x ↔ F(g) ∈ T_{F(x)}`. -/
theorem isotropyHom_mem_trivialSet_iff {x : Obj} (g : X.Isotropy x) :
    F.isotropyHom x g ∈ Y.trivialSet (F.obj x) ↔ g ∈ X.trivialSet x := by
  rw [← EpGroupoid.val_mem_nonEffectivePart_iff, ← EpGroupoid.val_mem_nonEffectivePart_iff,
    isotropyHom_val]
  exact ⟨F.mem_nonEffectivePart_of_mor hF (g.src_val.trans g.tgt_val.symm),
    F.mor_mem_nonEffectivePart hF⟩

end EpFunctor

namespace EpFunctor.IsEquivalence

variable {F : EpFunctor X Y} (hF : F.IsEquivalence)
include hF

/-- For an equivalence, `F : G_x → G_{F(x)}` is a group isomorphism. -/
theorem bijective_isotropyHom (x : Obj) : Bijective (F.isotropyHom x) := by
  refine ⟨fun g g' h => GroupoidStr.Isotropy.ext ?_, fun h => ?_⟩
  · exact hF.mor_injective (g.src_val.trans g'.src_val.symm) (g.tgt_val.trans g'.tgt_val.symm)
      (congrArg GroupoidStr.Isotropy.val h)
  · obtain ⟨φ, hs, ht, he⟩ := hF.exists_mor_eq h.src_val h.tgt_val
    exact ⟨⟨φ, hs, ht⟩, GroupoidStr.Isotropy.ext he⟩

/-- **2021 Remark 10.1.12, p. 472 (new in the 2021 edition)**: for an equivalence `F` and
`ψ : F(x) → y`, the isomorphism `G_x → G_y`, `g ↦ ψ ∘ F(g) ∘ ψ⁻¹`, maps `T_x` onto `T_y`. -/
theorem remark_10_1_12 {x : Obj} {y : Obj'} (ψ : Mor') (hs : Y.src ψ = F.obj x)
    (ht : Y.tgt ψ = y) : ∃ e : X.Isotropy x ≃* Y.Isotropy y,
      (∀ g, (e g).val = Y.comp (Y.comp ψ (F.mor g.val)) (Y.inv ψ)) ∧
      ∀ g, e g ∈ Y.trivialSet y ↔ g ∈ X.trivialSet x := by
  refine ⟨(MulEquiv.ofBijective _ (hF.bijective_isotropyHom x)).trans (Y.isotropyConj ψ hs ht),
    fun g => rfl, fun g => ?_⟩
  change Y.isotropyConj ψ hs ht (F.isotropyHom x g) ∈ Y.trivialSet y ↔ _
  rw [Y.isotropyConj_mem_trivialSet_iff]
  exact F.isotropyHom_mem_trivialSet_iff hF.isLocalScDiffeo_obj g

end EpFunctor.IsEquivalence

/-! ### Closedness of `𝐗^T` under equivalences -/

/-- The multiplication is continuous at `a` along composable families. -/
theorem EpGroupoid.continuousAt_comp {α : Type*} [TopologicalSpace α] (X : EpGroupoid Obj Mor)
    {f g : α → Mor} {a : α} (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (h : ∀ᶠ z in 𝓝 a, X.src (f z) = X.tgt (g z)) :
    ContinuousAt (fun z => X.comp (f z) (g z)) a := by
  have hS : ContinuousOn (fun q : Mor × Mor => X.comp q.1 q.2)
      (MPolyfold.fibredProduct X.src X.tgt) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact X.continuous_comp_fibredProduct
  have hpa : (f a, g a) ∈ MPolyfold.fibredProduct X.src X.tgt := h.self_of_nhds
  have ht : Tendsto (fun z => (f z, g z)) (𝓝 a)
      (𝓝[MPolyfold.fibredProduct X.src X.tgt] (f a, g a)) :=
    tendsto_nhdsWithin_iff.2 ⟨hf.prodMk_nhds hg, h⟩
  exact (hS _ hpa).tendsto.comp ht

namespace EpFunctor

/-- **`𝐗^T` is closed iff `𝐘^T` is closed** for an equivalence `F : X → Y` (the proofs of
Propositions 10.1.13 (2) and 10.1.16).  `⇐`: `𝐗^T = F⁻¹(𝐘^T) ∩ {s = t}`.  `⇒`: for
`ψ ∈ cl 𝐘^T` with `s ψ = t ψ = y` take `σ : F(x) → y`, conjugate by the local inverse `b` of `t`
at `σ`: `χ ↦ b(t χ)⁻¹ ∘ χ ∘ b(s χ)` is continuous at `ψ` and preserves `𝐘^T`, so
`σ⁻¹ ∘ ψ ∘ σ = F(φ) ∈ cl 𝐘^T`, `φ ∈ cl 𝐗^T = 𝐗^T` (`F` is open and injective near `x`), and
`ψ = σ ∘ F(φ) ∘ σ⁻¹ ∈ 𝐘^T`. -/
theorem IsEquivalence.isClosed_nonEffectivePart_iff {F : EpFunctor X Y} (hF : F.IsEquivalence) :
    IsClosed X.nonEffectivePart ↔ IsClosed Y.nonEffectivePart := by
  have hd := hF.isLocalScDiffeo_obj
  constructor
  · intro hX
    refine isClosed_of_closure_subset fun ψ hψ => ?_
    have hst : Y.src ψ = Y.tgt ψ :=
      closure_minimal (fun k hk => EpGroupoid.src_eq_tgt_of_mem_nonEffectivePart hk)
        (isClosed_eq Y.continuous_src Y.continuous_tgt) hψ
    obtain ⟨x, σ, hσs, hσt⟩ := hF.exists_iso (Y.src ψ)
    obtain ⟨W, V, b, hσW, hb⟩ := Y.isLocalScDiffeo_tgt σ
    have hbV : ∀ z ∈ V, Y.tgt (b z) = z := fun z hz => hb.right_inv z hz
    have hψV : Y.src ψ ∈ V := hσt ▸ hb.mapsTo hσW
    have hψV' : Y.tgt ψ ∈ V := hst ▸ hψV
    have hbψ : b (Y.src ψ) = σ := by rw [← hσt]; exact hb.left_inv σ hσW
    -- the conjugation `C`
    set C : Mor' → Mor' := fun χ => Y.comp (Y.inv (b (Y.tgt χ))) (Y.comp χ (b (Y.src χ)))
      with hC
    have hsV : ∀ᶠ χ in 𝓝 ψ, Y.src χ ∈ V :=
      (Y.continuous_src.tendsto ψ).eventually (hb.isOpen_target.mem_nhds hψV)
    have htV : ∀ᶠ χ in 𝓝 ψ, Y.tgt χ ∈ V :=
      (Y.continuous_tgt.tendsto ψ).eventually (hb.isOpen_target.mem_nhds hψV')
    have hbc : ∀ z ∈ V, ContinuousAt b z := fun z hz =>
      hb.isScSmoothOn_inv.continuousOn.continuousAt (hb.isOpen_target.mem_nhds hz)
    have hCc : ContinuousAt C ψ := by
      have h1 : ContinuousAt (fun χ => Y.comp χ (b (Y.src χ))) ψ :=
        Y.continuousAt_comp continuousAt_id ((hbc _ hψV).comp Y.continuous_src.continuousAt)
          (hsV.mono fun χ hχ => (hbV _ hχ).symm)
      refine Y.continuousAt_comp (Y.continuous_inv.continuousAt.comp
        ((hbc _ hψV').comp Y.continuous_tgt.continuousAt)) h1 ?_
      filter_upwards [hsV, htV] with χ hs ht
      rw [Y.src_inv, hbV _ ht, Y.tgt_comp _ _ (hbV _ hs).symm]
    have hCT : ∀ᶠ χ in 𝓝 ψ, χ ∈ Y.nonEffectivePart → C χ ∈ Y.nonEffectivePart := by
      filter_upwards [hsV] with χ hs hχ
      have := EpGroupoid.conj_mem_nonEffectivePart hχ (hbV _ hs).symm
      change Y.comp (Y.inv (b (Y.tgt χ))) (Y.comp χ (b (Y.src χ))) ∈ _
      rwa [← EpGroupoid.src_eq_tgt_of_mem_nonEffectivePart hχ]
    have hCψ : C ψ = Y.comp (Y.inv σ) (Y.comp ψ σ) := by
      change Y.comp (Y.inv (b (Y.tgt ψ))) (Y.comp ψ (b (Y.src ψ))) = _
      rw [← hst, hbψ]
    have hCcl : C ψ ∈ closure Y.nonEffectivePart := by
      have : (𝓝[Y.nonEffectivePart] ψ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hψ
      refine mem_closure_of_tendsto (b := 𝓝[Y.nonEffectivePart] ψ)
        (hCc.tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [nhdsWithin_le_nhds hCT, self_mem_nhdsWithin] with χ h1 h2
      exact h1 h2
    -- `C ψ = F(φ)` with `φ : x → x`
    have hσψ : Y.src ψ = Y.tgt σ := hσt.symm
    have hCs : Y.src (C ψ) = F.obj x := by
      rw [hCψ, Y.src_comp _ _ (by rw [Y.src_inv, Y.tgt_comp _ _ hσψ, hσt, hst]),
        Y.src_comp _ _ hσψ, hσs]
    have hCt : Y.tgt (C ψ) = F.obj x := by
      rw [hCψ, Y.tgt_comp _ _ (by rw [Y.src_inv, Y.tgt_comp _ _ hσψ, hσt, hst]), Y.tgt_inv, hσs]
    obtain ⟨φ, hφs, hφt, hφ⟩ := hF.exists_mor_eq hCs hCt
    -- `φ ∈ cl 𝐗^T = 𝐗^T`
    have hφcl : φ ∈ closure (F.mor ⁻¹' Y.nonEffectivePart) :=
      (F.isLocalScDiffeo_mor hd).isOpenMap.preimage_closure_subset_closure_preimage
        (show F.mor φ ∈ closure Y.nonEffectivePart by rw [hφ]; exact hCcl)
    obtain ⟨U, V', g, hxU, hU⟩ := hd x
    set N : Set Mor := X.src ⁻¹' U ∩ X.tgt ⁻¹' U with hN
    have hNo : IsOpen N := (hU.isOpen_source.preimage X.continuous_src).inter
      (hU.isOpen_source.preimage X.continuous_tgt)
    have hφN : φ ∈ N := ⟨by rw [mem_preimage, hφs]; exact hxU, by rw [mem_preimage, hφt]; exact hxU⟩
    have hNsub : N ∩ F.mor ⁻¹' Y.nonEffectivePart ⊆ X.nonEffectivePart := by
      rintro φ' ⟨⟨hs', ht'⟩, hT⟩
      have hst' : X.src φ' = X.tgt φ' := by
        refine hU.injOn hs' ht' ?_
        rw [← F.src_mor, ← F.tgt_mor]
        exact EpGroupoid.src_eq_tgt_of_mem_nonEffectivePart hT
      exact F.mem_nonEffectivePart_of_mor hd hst' hT
    have hφT : φ ∈ X.nonEffectivePart := by
      rw [← hX.closure_eq]
      exact closure_mono hNsub (hNo.inter_closure ⟨hφN, hφcl⟩)
    -- back to `ψ`
    have hCT' : C ψ ∈ Y.nonEffectivePart := by
      rw [← hφ]
      exact F.mor_mem_nonEffectivePart hd hφT
    have hsC : Y.src (C ψ) = Y.tgt (Y.inv σ) := by rw [hCs, Y.tgt_inv, hσs]
    have key := EpGroupoid.conj_mem_nonEffectivePart hCT' hsC
    have he : Y.comp (C ψ) (Y.inv σ) = Y.comp (Y.inv σ) ψ := by
      rw [hCψ, Y.comp_assoc _ _ _ (by rw [Y.src_inv, Y.tgt_comp _ _ hσψ, hσt, hst])
        (by rw [Y.src_comp _ _ hσψ, Y.tgt_inv]),
        GroupoidStr.comp_inv_cancel_right hσψ]
    rwa [he, GroupoidStr.inv_comp_cancel_left (by rw [Y.src_inv, hσt, hst])] at key
  · intro hY
    rw [F.nonEffectivePart_eq hd]
    exact (hY.preimage F.continuous_mor).inter (isClosed_eq X.continuous_src X.continuous_tgt)

/-- **2021 Proposition 10.1.16, p. 474 (new in the 2021 edition)**: if `F : X → Y` is an
equivalence, `X` has the local unique continuation property iff `Y` has it. -/
theorem proposition_10_1_16 {F : EpFunctor X Y} (hF : F.IsEquivalence) :
    X.IsLUC ↔ Y.IsLUC := by
  rw [X.proposition_7_2_21, Y.proposition_7_2_21]
  exact hF.isClosed_nonEffectivePart_iff

/-! ### Proposition 10.1.13: the reduced morphism spaces -/

variable (F : EpFunctor X Y) (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj)

/-- The map `F_R : 𝐗^R → 𝐘^R`, `[φ] ↦ [F(φ)]`, for a functor which is a local
sc-diffeomorphism on objects. -/
def reducedMap : X.ReducedMor → Y.ReducedMor :=
  Quot.lift (fun φ => Y.reducedπ (F.mor φ)) fun φ φ' h => by
    obtain ⟨ht, hk⟩ := X.reducedπ_eq_iff_comp_inv.1 (X.reducedπ_eq_iff.2 h)
    refine Y.reducedπ_eq_iff_comp_inv.2 ⟨by rw [F.tgt_mor, F.tgt_mor, ht], ?_⟩
    have hc : X.src (X.inv φ') = X.tgt φ := by rw [X.src_inv, ht]
    rw [← F.mor_inv, ← F.mor_comp _ _ hc]
    exact F.mor_mem_nonEffectivePart hF hk

@[simp]
theorem reducedMap_π (φ : Mor) : F.reducedMap hF (X.reducedπ φ) = Y.reducedπ (F.mor φ) := rfl

theorem continuous_reducedMap : Continuous (F.reducedMap hF) :=
  continuous_quot_lift _ (Y.continuous_reducedπ.comp F.continuous_mor)

theorem isOpenMap_reducedMap : IsOpenMap (F.reducedMap hF) := by
  intro O hO
  have he : F.reducedMap hF '' O = Y.reducedπ '' (F.mor '' (X.reducedπ ⁻¹' O)) := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
      exact ⟨F.mor φ, ⟨φ, hq, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
      exact ⟨X.reducedπ φ, hφ, rfl⟩
  rw [he]
  exact Y.isOpenMap_reducedπ _
    ((F.isLocalScDiffeo_mor hF).isOpenMap _ (hO.preimage X.continuous_reducedπ))

/-- **2021 Proposition 10.1.13, p. 472 (new in the 2021 edition)**: for an equivalence
`F : X → Y`, (1) `F_R : 𝐗^R → 𝐘^R` is continuous and open, (2) `𝐗^R` is Hausdorff iff `𝐘^R`
is. -/
theorem proposition_10_1_13 {F : EpFunctor X Y} (hF : F.IsEquivalence) :
    (Continuous (F.reducedMap hF.isLocalScDiffeo_obj) ∧
      IsOpenMap (F.reducedMap hF.isLocalScDiffeo_obj)) ∧
      (T2Space X.ReducedMor ↔ T2Space Y.ReducedMor) := by
  refine ⟨⟨F.continuous_reducedMap _, F.isOpenMap_reducedMap _⟩, ?_⟩
  rw [X.proposition_7_2_17, Y.proposition_7_2_17]
  exact hF.isClosed_nonEffectivePart_iff

/-! ### Proposition 10.1.14: the reduced functor -/

/-- `F_R` as a functor of the reduced groupoids (`F_R = F` on objects). -/
def reducedGroupoidFunctor : GroupoidFunctor X.reducedGroupoidStr Y.reducedGroupoidStr where
  obj := F.obj
  mor := F.reducedMap hF
  src_mor q := Quot.inductionOn q fun φ => F.src_mor φ
  tgt_mor q := Quot.inductionOn q fun φ => F.tgt_mor φ
  mor_comp q q' := Quot.inductionOn q fun φ => Quot.inductionOn q' fun φ' h => by
    have h' : X.src φ = X.tgt φ' := h
    have h'' : Y.src (F.mor φ) = Y.tgt (F.mor φ') := by rw [F.src_mor, F.tgt_mor, h']
    change F.reducedMap hF (X.reducedComp (X.reducedπ φ) (X.reducedπ φ')) =
      Y.reducedComp (Y.reducedπ (F.mor φ)) (Y.reducedπ (F.mor φ'))
    rw [X.reducedComp_π h', Y.reducedComp_π h'', reducedMap_π, F.mor_comp _ _ h']
  mor_unit x := congrArg Y.reducedπ (F.mor_unit x)

variable [T2Space X.ReducedMor] [T2Space Y.ReducedMor]

/-- **The reduced functor** `F_R : X_R → Y_R` (Proposition 10.1.14), an sc-smooth functor of the
reduced ep-groupoids. -/
def reduced : EpFunctor X.reducedEpGroupoid Y.reducedEpGroupoid :=
  EpFunctor.ofContinuous (F.reducedGroupoidFunctor hF) F.isScSmoothMap_obj
    (F.continuous_reducedMap hF)

omit [T2Space X.ReducedMor] [T2Space Y.ReducedMor] in
theorem reducedπ_eq_of_mor {F : EpFunctor X Y} (hF : F.IsEquivalence) {φ φ' : Mor}
    (hs : X.src φ = X.src φ') (ht : X.tgt φ = X.tgt φ')
    (h : Y.reducedπ (F.mor φ) = Y.reducedπ (F.mor φ')) : X.reducedπ φ = X.reducedπ φ' := by
  obtain ⟨-, hk⟩ := Y.reducedπ_eq_iff_comp_inv.1 h
  have hc : X.src (X.inv φ') = X.tgt φ := by rw [X.src_inv, ht]
  rw [← F.mor_inv, ← F.mor_comp _ _ hc] at hk
  refine X.reducedπ_eq_iff_comp_inv.2 ⟨ht, F.mem_nonEffectivePart_of_mor
    hF.isLocalScDiffeo_obj ?_ hk⟩
  rw [X.src_comp _ _ hc, X.tgt_comp _ _ hc, X.tgt_inv, hs]

/-- **2021 Proposition 10.1.14, p. 473 (2017: Proposition 10.5, p. 341)**: for an equivalence
`F : X → Y` with Hausdorff reduced morphism spaces, `F_R : X_R → Y_R` (`F_R = F` on objects,
`F_R([φ]) = [F(φ)]`) is a well-defined functor and an equivalence of ep-groupoids. -/
theorem proposition_10_1_14 {F : EpFunctor X Y} (hF : F.IsEquivalence) :
    (F.reduced hF.isLocalScDiffeo_obj).IsEquivalence := by
  refine (F.reduced hF.isLocalScDiffeo_obj).lemma_10_1_2
    { faithful := (GroupoidFunctor.faithful_iff _).2 fun q q' => ?_
      full := (GroupoidFunctor.full_iff _).2 fun x x' q => ?_
      essSurj := (GroupoidFunctor.essSurj_iff _).2 fun y => ?_ } hF.isLocalScDiffeo_obj
  · induction q using Quot.inductionOn with | h φ => ?_
    induction q' using Quot.inductionOn with | h φ' => ?_
    intro hs ht he
    exact reducedπ_eq_of_mor hF hs ht he
  · induction q using Quot.inductionOn with | h ψ => ?_
    intro hs ht
    obtain ⟨φ, hφs, hφt, hφ⟩ := hF.exists_mor_eq (x := x) (x' := x') hs ht
    exact ⟨X.reducedπ φ, hφs, hφt, congrArg Y.reducedπ hφ⟩
  · obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso y
    exact ⟨x, Y.reducedπ ψ, hs, ht⟩

end EpFunctor

/-! ### Proposition 10.1.18: the index lifts -/

namespace EpFunctor

/-- **The lift `F¹ : X¹ → Y¹`** of an sc-smooth functor (`F` restricted to level `1`). -/
def liftOne (F : EpFunctor X Y) : EpFunctor X.liftOne Y.liftOne where
  obj := MPolyfold.levelOneMap X.PObj Y.PObj F.obj (F.isScSmoothMap_obj.mapsTo_levelSet 1)
  mor := MPolyfold.levelOneMap X.PMor Y.PMor F.mor (F.isScSmoothMap_mor.mapsTo_levelSet 1)
  src_mor φ := MPolyfold.level_ext (F.src_mor (X.PMor.levelVal 1 φ))
  tgt_mor φ := MPolyfold.level_ext (F.tgt_mor (X.PMor.levelVal 1 φ))
  mor_comp φ ψ h := by
    have h' : X.src (X.PMor.levelVal 1 φ) = X.tgt (X.PMor.levelVal 1 ψ) :=
      congrArg (X.PObj.levelVal 1) h
    have h'' : Y.liftOne.src (MPolyfold.levelOneMap X.PMor Y.PMor F.mor
        (F.isScSmoothMap_mor.mapsTo_levelSet 1) φ) = Y.liftOne.tgt (MPolyfold.levelOneMap
        X.PMor Y.PMor F.mor (F.isScSmoothMap_mor.mapsTo_levelSet 1) ψ) :=
      MPolyfold.level_ext (by
        rw [Y.liftOne_src_val, Y.liftOne_tgt_val, MPolyfold.levelVal_levelOneMap,
          MPolyfold.levelVal_levelOneMap, F.src_mor, F.tgt_mor, h'])
    refine MPolyfold.level_ext ?_
    rw [Y.liftOne_comp_val h'', MPolyfold.levelVal_levelOneMap, MPolyfold.levelVal_levelOneMap,
      MPolyfold.levelVal_levelOneMap, X.liftOne_comp_val h, F.mor_comp _ _ h']
  mor_unit x := MPolyfold.level_ext (F.mor_unit (X.PObj.levelVal 1 x))
  isScSmoothMap_obj := MPolyfold.IsScSmoothMap.levelOne F.isScSmoothMap_obj fun _ => rfl
  isScSmoothMap_mor := MPolyfold.IsScSmoothMap.levelOne F.isScSmoothMap_mor fun _ => rfl

/-- **The lift of an equivalence is an equivalence** (the proof of Proposition 10.1.18). -/
theorem IsEquivalence.liftOne {F : EpFunctor X Y} (hF : F.IsEquivalence) :
    F.liftOne.IsEquivalence := by
  have hd := hF.isLocalScDiffeo_obj
  refine F.liftOne.lemma_10_1_2
    { faithful := (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs ht he =>
        MPolyfold.level_ext (hF.mor_injective (congrArg (X.PObj.levelVal 1) hs)
          (congrArg (X.PObj.levelVal 1) ht) (congrArg (Y.PMor.levelVal 1) he))
      full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => ?_
      essSurj := (GroupoidFunctor.essSurj_iff _).2 fun y => ?_ } hd.levelOne
  · have hs' : Y.src (Y.PMor.levelVal 1 ψ) = F.obj (X.PObj.levelVal 1 x) :=
      congrArg (Y.PObj.levelVal 1) hs
    have ht' : Y.tgt (Y.PMor.levelVal 1 ψ) = F.obj (X.PObj.levelVal 1 x') :=
      congrArg (Y.PObj.levelVal 1) ht
    obtain ⟨φ, hφs, hφt, hφ⟩ := hF.exists_mor_eq hs' ht'
    have hφ1 : φ ∈ X.PMor.levelSet 1 :=
      (X.mem_levelSet_src_iff φ 1).1 (hφs ▸ MPolyfold.levelVal_mem x)
    refine ⟨X.PMor.levelMk 1 φ hφ1, MPolyfold.level_ext ?_, MPolyfold.level_ext ?_,
      MPolyfold.level_ext ?_⟩
    · rw [X.liftOne_src_val, MPolyfold.levelVal_levelMk, hφs]
    · rw [X.liftOne_tgt_val, MPolyfold.levelVal_levelMk, hφt]
    · change F.mor (X.PMor.levelVal 1 (X.PMor.levelMk 1 φ hφ1)) = _
      rw [MPolyfold.levelVal_levelMk, hφ]
  · obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso (Y.PObj.levelVal 1 y)
    have hψ1 : ψ ∈ Y.PMor.levelSet 1 :=
      (Y.mem_levelSet_tgt_iff ψ 1).1 (ht ▸ MPolyfold.levelVal_mem y)
    have hx1 : x ∈ X.PObj.levelSet 1 :=
      (hd.mem_levelSet_iff x 1).1 (hs ▸ (Y.mem_levelSet_src_iff ψ 1).2 hψ1)
    refine ⟨X.PObj.levelMk 1 x hx1, Y.PMor.levelMk 1 ψ hψ1, MPolyfold.level_ext ?_,
      MPolyfold.level_ext ?_⟩
    · change Y.src ψ = F.obj (X.PObj.levelVal 1 (X.PObj.levelMk 1 x hx1))
      rw [MPolyfold.levelVal_levelMk, hs]
    · rw [Y.liftOne_tgt_val, MPolyfold.levelVal_levelMk, ht]

end EpFunctor

end Reduced

/-- **The lifts `Fⁱ : Xⁱ → Yⁱ` of an equivalence are equivalences** (the proof of
Proposition 10.1.18). -/
theorem EP.exists_isEquivalence_lift {A B : EP.{u}} {F : EpFunctor A.X B.X}
    (hF : F.IsEquivalence) (i : ℕ) :
    ∃ G : EpFunctor (A.lift i).X (B.lift i).X, G.IsEquivalence := by
  induction i with
  | zero => exact ⟨F, hF⟩
  | succ i ih =>
    obtain ⟨G, hG⟩ := ih
    exact ⟨G.liftOne, hG.liftOne⟩

/-- **2021 Proposition 10.1.18, p. 476 (new in the 2021 edition)**: if `F : X → Y` is an
equivalence, `X` satisfies (SLUC) iff `Y` does (Proposition 10.1.16 applied to the lifts). -/
theorem EP.proposition_10_1_18 {A B : EP.{u}} {F : EpFunctor A.X B.X} (hF : F.IsEquivalence) :
    A.IsSLUC ↔ B.IsSLUC :=
  ⟨fun h i => by
    obtain ⟨G, hG⟩ := EP.exists_isEquivalence_lift hF i
    exact (EpFunctor.proposition_10_1_16 hG).1 (h i),
  fun h i => by
    obtain ⟨G, hG⟩ := EP.exists_isEquivalence_lift hF i
    exact (EpFunctor.proposition_10_1_16 hG).2 (h i)⟩

end Polyfold
