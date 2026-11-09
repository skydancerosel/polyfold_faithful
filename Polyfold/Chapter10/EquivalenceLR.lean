import Polyfold.Chapter10.EquivalenceZhou
import Polyfold.Chapter10.WeakFibredProduct

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.1 "Equivalences", pp. 467–472 and 477: **Proposition 10.1.9** (p. 468,
new in the 2021 edition), **Proposition 10.1.10** (p. 470; 2017: Proposition 10.4, p. 340) and
**Proposition 10.1.19** (p. 477, new in the 2021 edition).  Numbers and pages are the 2021 text's.

# The local regularity property under equivalences

## The text, paraphrased

(Discussion before Proposition 10.1.9, pp. 467–468, and (10.1)–(10.3).)  For an equivalence
`F : X → Y` and a morphism `ψ : F(x) → y`, the composition `Q = ψ̂ ∘ F` of `F` near `x` and of
`ψ̂ = t ∘ (s|𝐔(ψ))⁻¹` near `F(x)` is an sc-diffeomorphism of a neighbourhood of `x` onto one of
`y`, and `g ↦ ψ ∘ F(g) ∘ ψ⁻¹` is an isomorphism `G_x → G_y` with `Q(g ∗ z) = Q(g) ∗ Q(z)`.

(Proposition 10.1.9) If `F : X → Y` is an equivalence and one of `X`, `Y` has the local
regularity property (LR) (Definition 7.4.19), so does the other.  *Proof* (text): if `X` has
(LR), take `ψ : F(x) → y`, a neighbourhood `U(x)` as in (LR) and `U(y) = Q(U(x))`; an
sc-diffeomorphism `γ` of `U(y)` preserving orbits gives `β = Q⁻¹ ∘ γ ∘ Q = ĝ`, hence
`γ = (ψ ∘ F(g) ∘ ψ⁻¹)^`.  If `Y` has (LR), take `y = F(x)` and conjugate `β` by `F` instead.

(Proposition 10.1.10) If `X` and `Y` have (LR) and `F, G : X → Y` are equivalences with
`|F| = |G|`, then (1) every `x` has a connected neighbourhood `U(x)` with the natural `G_x`-action
and an sc-smooth `z ↦ α_z : F(z) → G(z)` on it; (2) `|TF| = |TG|`.  *Proof* (text): with
`ψ : F(x) → G(x)`, the composition `β = G⁻¹ ∘ ψ̂ ∘ F` of (10.4) is an sc-diffeomorphism near
`x` with `|β(z)| = |z|`; Lemma 7.4.20 makes it a diffeomorphism of `U(x)`, so (LR) gives
`β = ĝ`, and `α_z = G(Γ(g, z))⁻¹ ∘ ψ_z`.  Differentiating `α` at `x` gives (2).

(Proposition 10.1.19) (SLR) passes along equivalences, by Proposition 10.1.9 for the lifts.

## What is formalized

* `NaturalRep.HasLR` (the condition of (LR) on one `U(x)`), `isLR_iff_hasLR`; uniqueness of `Γ`
  and of the action on preconnected sets through `x` (`NaturalRep.eqOn_Γ`, `eqOn_Φ`).
* `NaturalRep.hasLR_iff_of_equivariant`: the two conjugation arguments of the proof, for any
  equivariant sc-diffeomorphism `U(x) → U(y)` along a surjection `G_x → G_y`.
* `EpFunctor.TransportChart` (the data `Q = ψ̂ ∘ F`, `ψ_u : F(u) → Q(u)`), its existence
  `exists_transportChart`, the isomorphism `TransportChart.conj` (`ψ ∘ F(g) ∘ ψ⁻¹`) with
  `bijective_conj`, and the equivariance (10.2)–(10.3) `TransportChart.Q_Φ`.  Witnesses:
  `TransportChart.nonempty` and `EquivalenceLRExamples.nonempty_transportChart_pointEP`.
* `TransportChart.exists_naturalRep_push`, `exists_naturalRep_pull`: natural representations
  carried along `Q`.
* `EpFunctor.proposition_10_1_9` (**Proposition 10.1.9**).
* `EpFunctor.proposition_10_1_10_one`, `proposition_10_1_10_one_of_isLR_right` (**(1)**) and
  `EpFunctor.proposition_10_1_10_two` (**(2)**); hypotheses satisfiable:
  `EquivalenceLRExamples.proposition_10_1_10_hypotheses`.
* `EP.proposition_10_1_19` (**Proposition 10.1.19**), from `EP.isSLR_iff_of_isLR_iff`.

## What the text leaves implicit, and the choices made

* The text takes `U(y) = Q(U(x))` "with the natural action" of `G_y`.  That `Q(U(x))` carries a
  natural representation is the content of `exists_naturalRep_push`: it restricts an arbitrary
  natural representation at `y` (Theorem 7.1.13) to `Q(U(x))`; invariance under `G_y` comes from
  the equivariance `Q(g ∗ z) = (ψ ∘ F(g) ∘ ψ⁻¹) ∗ Q(z)` and surjectivity of `g ↦ ψ ∘ F(g) ∘ ψ⁻¹`.
  No transport of `Γ` is needed.  The converse direction restricts a natural representation at `x`
  to `Q⁻¹(U(y))` (`exists_naturalRep_pull`), using the uniqueness `eqOn_Φ` on the connected
  `U(y)`.  The equivariance is proved from the uniqueness of `Γ` (`eqOn_Γ`) on connected sets.
* Definition 7.4.19 asks for arbitrarily small `U(x)`; the proofs give them, and Proposition
  10.1.10 (1) is stated with `U(x) ⊆ O` for any open `O ∋ x`.
* Proposition 10.1.10 assumes (LR) for both `X` and `Y`; the proof uses it only for `X`, which is
  the hypothesis of `proposition_10_1_10_one`.  With (LR) for `Y` only, Proposition 10.1.9 applies
  (`proposition_10_1_10_one_of_isLR_right`, as the text remarks after the proof of 10.1.9).
* `|TF| = |TG|` is the equality of the orbit maps of the tangent functors `F.tangent`,
  `G.tangent` (Chapter 8), and `Tα` is `MPolyfold.tangentMapOn`.
* On p. 469 the isomorphism `σ ↦ ψ ∘ σ ∘ ψ⁻¹` is written with target `U(y)`; we read `G_y`
  (possible misprint).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### Helpers -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- `p ↦ a(p) ∘ b(p)` is continuous on a set on which `a`, `b` are continuous and
`s(a(p)) = t(b(p))`. -/
theorem continuousOn_comp_of {α : Type*} [TopologicalSpace α] {a b : α → Mor} {S : Set α}
    (ha : ContinuousOn a S) (hb : ContinuousOn b S) (hab : ∀ p ∈ S, X.src (a p) = X.tgt (b p)) :
    ContinuousOn (fun p => X.comp (a p) (b p)) S := by
  have hS : ContinuousOn (fun q : Mor × Mor => X.comp q.1 q.2)
      (MPolyfold.fibredProduct X.src X.tgt) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact X.continuous_comp_fibredProduct
  exact hS.comp (ha.prodMk hb) hab

namespace NaturalRep

variable {X} {x : Obj}

/-- The property of the neighbourhood `U(x)` in (LR) (2021 Definition 7.4.19): every
sc-diffeomorphism `β` of `U(x)` with `|β(y)| = |y|` is `ĝ` for some `g ∈ G_x`. -/
def HasLR (R : X.NaturalRep x) : Prop :=
  ∀ β β' : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj β β' R.U R.U →
    (∀ y ∈ R.U, X.π (β y) = X.π y) → ∃ g : X.Isotropy x, ∀ y ∈ R.U, β y = R.Φ g y

/-- **Uniqueness of `Γ`**: two natural representations at `x` have the same `Γ(g, ·)` on every
preconnected `V ∋ x` inside both neighbourhoods (both are continuous sections of `s` through
`g`). -/
theorem eqOn_Γ (R R₂ : X.NaturalRep x) {V : Set Obj} (hV : IsPreconnected V) (hxV : x ∈ V)
    (hV₁ : V ⊆ R.U) (hV₂ : V ⊆ R₂.U) (g : X.Isotropy x) : EqOn (R.Γ g) (R₂.Γ g) V :=
  eqOn_sections_of_isPreconnected X.isLocalScDiffeo_src.isLocallyInjective hV
    ((R.isScSmoothOn_Γ g).continuousOn.mono hV₁) ((R₂.isScSmoothOn_Γ g).continuousOn.mono hV₂)
    (fun y hy => R.src_Γ g y (hV₁ hy)) (fun y hy => R₂.src_Γ g y (hV₂ hy)) hxV
    ((R.Γ_self g).trans (R₂.Γ_self g).symm)

/-- **Uniqueness of the natural action**: two natural representations at `x` have the same
`Φ(g)` on every preconnected `V ∋ x` inside both neighbourhoods. -/
theorem eqOn_Φ (R R₂ : X.NaturalRep x) {V : Set Obj} (hV : IsPreconnected V) (hxV : x ∈ V)
    (hV₁ : V ⊆ R.U) (hV₂ : V ⊆ R₂.U) (g : X.Isotropy x) : EqOn (R.Φ g) (R₂.Φ g) V :=
  fun y hy => by
    rw [← R.tgt_Γ g y (hV₁ hy), ← R₂.tgt_Γ g y (hV₂ hy), R.eqOn_Γ R₂ hV hxV hV₁ hV₂ g hy]

end NaturalRep

/-- (LR) in terms of `NaturalRep.HasLR`. -/
theorem isLR_iff_hasLR : X.IsLR ↔ ∀ (x : Obj) (O : Set Obj), IsOpen O → x ∈ O →
    ∃ R : X.NaturalRep x, R.U ⊆ O ∧ R.HasLR :=
  Iff.rfl

end EpGroupoid

section Transport

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- **(LR) for conjugate natural representations**: if an sc-diffeomorphism `Q : U(x) → U(y)`
intertwines the natural actions along a surjection `e : G_x → G_y` and preserves and reflects
orbit equality, then `U(x)` has the property of (LR) iff `U(y)` has it (`β = Q⁻¹ ∘ γ ∘ Q`,
`γ = Q ∘ β ∘ Q⁻¹`). -/
theorem EpGroupoid.NaturalRep.hasLR_iff_of_equivariant {x : Obj} {y : Obj'}
    (R : X.NaturalRep x) (R' : Y.NaturalRep y) {Q : Obj → Obj'} {Q' : Obj' → Obj}
    (hQ : X.PObj.IsScDiffeoOn Y.PObj Q Q' R.U R'.U) (e : X.Isotropy x → Y.Isotropy y)
    (he : Surjective e) (hQΦ : ∀ g, ∀ u ∈ R.U, Q (R.Φ g u) = R'.Φ (e g) (Q u))
    (hπ : ∀ a ∈ R.U, ∀ b ∈ R.U, X.π a = X.π b ↔ Y.π (Q a) = Y.π (Q b)) :
    R.HasLR ↔ R'.HasLR := by
  constructor
  · intro h γ γ' hγ hγπ
    obtain ⟨g, hg⟩ := h _ _ (hQ.symm.comp (hγ.comp hQ)) fun u hu => by
      have hQu := hQ.mapsTo hu
      have hγu := hγ.mapsTo hQu
      refine (hπ _ (hQ.mapsTo_inv hγu) u hu).2 ?_
      rw [hQ.right_inv _ hγu]
      exact hγπ _ hQu
    refine ⟨e g, fun z hz => ?_⟩
    have hz' := hQ.mapsTo_inv hz
    have h1 := hg _ hz'
    simp only [Function.comp_apply, hQ.right_inv z hz] at h1
    calc γ z = Q (Q' (γ z)) := (hQ.right_inv _ (hγ.mapsTo hz)).symm
      _ = Q (R.Φ g (Q' z)) := by rw [h1]
      _ = R'.Φ (e g) (Q (Q' z)) := hQΦ g _ hz'
      _ = R'.Φ (e g) z := by rw [hQ.right_inv z hz]
  · intro h β β' hβ hβπ
    obtain ⟨k, hk⟩ := h _ _ (hQ.comp (hβ.comp hQ.symm)) fun z hz => by
      have hz' := hQ.mapsTo_inv hz
      have h1 := (hπ _ (hβ.mapsTo hz') _ hz').1 (hβπ _ hz')
      simp only [Function.comp_apply]
      rwa [hQ.right_inv z hz] at h1
    obtain ⟨g, rfl⟩ := he k
    refine ⟨g, fun u hu => ?_⟩
    have h1 := hk _ (hQ.mapsTo hu)
    simp only [Function.comp_apply, hQ.left_inv u hu] at h1
    rw [← hQΦ g u hu] at h1
    calc β u = Q' (Q (β u)) := (hQ.left_inv _ (hβ.mapsTo hu)).symm
      _ = Q' (Q (R.Φ g u)) := by rw [h1]
      _ = R.Φ g u := hQ.left_inv _ (R.mapsTo_Φ g hu)

namespace EpFunctor

variable (F : EpFunctor X Y)

/-- **The chart `Q` along a morphism `ψ : F(x) → y`** (2021 pp. 467–468 and (10.1)): an
sc-diffeomorphism `Q = ψ̂ ∘ F = t ∘ (s|𝐔(ψ))⁻¹ ∘ F` of an open `W ∋ x` onto an open `W' ∋ y`,
with the sc-smooth family `ψ_u = (s|𝐔(ψ))⁻¹(F u) : F(u) → Q(u)`, `ψ_x = ψ`. -/
structure TransportChart (x : Obj) (y : Obj') where
  /-- The morphism `ψ : F(x) → y`. -/
  ψ₀ : Mor'
  src_ψ₀ : Y.src ψ₀ = F.obj x
  tgt_ψ₀ : Y.tgt ψ₀ = y
  /-- The open neighbourhood `W` of `x`. -/
  W : Set Obj
  /-- Its image `W' = Q(W)`. -/
  W' : Set Obj'
  /-- The chart `Q : W → W'`. -/
  Q : Obj → Obj'
  /-- The inverse `Q⁻¹ : W' → W`. -/
  Qinv : Obj' → Obj
  /-- The family `ψ_u : F(u) → Q(u)`. -/
  ψ : Obj → Mor'
  mem_W : x ∈ W
  isScDiffeoOn_Q : X.PObj.IsScDiffeoOn Y.PObj Q Qinv W W'
  isScSmoothOn_ψ : X.PObj.IsScSmoothOn Y.PMor ψ W
  src_ψ : ∀ u ∈ W, Y.src (ψ u) = F.obj u
  tgt_ψ : ∀ u ∈ W, Y.tgt (ψ u) = Q u
  ψ_self : ψ x = ψ₀

variable {F}

/-- **The chart along `ψ` exists** whenever `F` is a local sc-diffeomorphism on objects: `F` at
`x`, `(s|𝐔(ψ))⁻¹` at `F(x)` and `t` at `ψ` are local sc-diffeomorphisms. -/
theorem exists_transportChart (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) {x : Obj} {y : Obj'}
    {ψ₀ : Mor'} (hs : Y.src ψ₀ = F.obj x) (ht : Y.tgt ψ₀ = y) :
    ∃ T : F.TransportChart x y, T.ψ₀ = ψ₀ := by
  obtain ⟨N, S, σ, hψN, hσ⟩ := Y.isLocalScDiffeo_src ψ₀
  have hFxS : F.obj x ∈ S := hs ▸ hσ.mapsTo hψN
  have hσx : σ (F.obj x) = ψ₀ := by rw [← hs]; exact hσ.left_inv ψ₀ hψN
  have h1 : X.PObj.IsLocalScDiffeoAt Y.PMor (σ ∘ F.obj) x :=
    (hσ.symm.isLocalScDiffeoAt hFxS).comp (hF.at x)
  have h2 : X.PObj.IsLocalScDiffeoAt Y.PObj (Y.tgt ∘ (σ ∘ F.obj)) x := by
    refine MPolyfold.IsLocalScDiffeoAt.comp ?_ h1
    rw [Function.comp_apply, hσx]
    exact Y.isLocalScDiffeo_tgt.at ψ₀
  obtain ⟨W₁, W₁', Qinv, hxW₁, hd⟩ := h2
  have hWo : IsOpen (W₁ ∩ F.obj ⁻¹' S) :=
    hd.isOpen_source.inter (hσ.isOpen_target.preimage F.continuous_obj')
  refine ⟨⟨ψ₀, hs, ht, W₁ ∩ F.obj ⁻¹' S, _, Y.tgt ∘ (σ ∘ F.obj), Qinv, σ ∘ F.obj, ⟨hxW₁, hFxS⟩,
    hd.restrict hWo inter_subset_left, ?_, fun u hu => hσ.right_inv _ hu.2, fun u _ => rfl,
    hσx⟩, rfl⟩
  exact MPolyfold.IsScSmoothOn.comp hσ.isScSmoothOn_inv
    (F.isScSmoothMap_obj.mono hWo (subset_univ _)) fun u hu => hu.2

namespace TransportChart

variable {x : Obj} {y : Obj'} (T : F.TransportChart x y)

theorem isOpen_W : IsOpen T.W := T.isScDiffeoOn_Q.isOpen_source

theorem isOpen_W' : IsOpen T.W' := T.isScDiffeoOn_Q.isOpen_target

/-- `Q(x) = y`. -/
theorem Q_self : T.Q x = y := by rw [← T.tgt_ψ x T.mem_W, T.ψ_self, T.tgt_ψ₀]

theorem mem_W' : y ∈ T.W' := by
  have h := T.isScDiffeoOn_Q.mapsTo T.mem_W
  rwa [T.Q_self] at h

theorem continuousOn_Q : ContinuousOn T.Q T.W := T.isScDiffeoOn_Q.isScSmoothOn.continuousOn

theorem continuousOn_ψ : ContinuousOn T.ψ T.W := T.isScSmoothOn_ψ.continuousOn

/-- `Q` is an sc-diffeomorphism of every open `U ⊆ W` onto `Q(U)`. -/
theorem isScDiffeoOn_image {U : Set Obj} (hU : IsOpen U) (hUW : U ⊆ T.W) :
    X.PObj.IsScDiffeoOn Y.PObj T.Q T.Qinv U (T.Q '' U) := by
  have h := T.isScDiffeoOn_Q.restrict hU hUW
  have e := h.image_eq
  rw [← e] at h
  exact h

/-- **The isotropy homomorphism** `G_x → G_y`, `g ↦ ψ ∘ F(g) ∘ ψ⁻¹` (2021 p. 469, the text's
`Q`; Remark 10.1.12). -/
def conj : X.Isotropy x →* Y.Isotropy y :=
  (Y.isotropyConj T.ψ₀ T.src_ψ₀ T.tgt_ψ₀).toMonoidHom.comp (F.isotropyHom x)

theorem conj_val (g : X.Isotropy x) :
    (T.conj g).val = Y.comp (Y.comp T.ψ₀ (F.mor g.val)) (Y.inv T.ψ₀) :=
  rfl

/-- For an equivalence, `g ↦ ψ ∘ F(g) ∘ ψ⁻¹` is a group isomorphism (Remark 10.1.12). -/
theorem bijective_conj (hF : F.IsEquivalence) : Bijective T.conj :=
  (Y.isotropyConj T.ψ₀ T.src_ψ₀ T.tgt_ψ₀).bijective.comp (hF.bijective_isotropyHom x)

/-- `|Q(u)| = |F(u)|` (through `ψ_u`). -/
theorem π_Q {u : Obj} (hu : u ∈ T.W) : Y.π (T.Q u) = Y.π (F.obj u) :=
  (Y.π_eq_π_iff.2 ⟨T.ψ u, T.src_ψ u hu, T.tgt_ψ u hu⟩).symm

/-- For a full `F`, `Q` preserves and reflects orbit equality: `|a| = |b|` iff
`|Q(a)| = |Q(b)|`. -/
theorem π_eq_π_iff (hF : F.toFunctor.Full) {a b : Obj} (ha : a ∈ T.W) (hb : b ∈ T.W) :
    X.π a = X.π b ↔ Y.π (T.Q a) = Y.π (T.Q b) := by
  rw [T.π_Q ha, T.π_Q hb, ← F.orbitMap_π, ← F.orbitMap_π]
  exact (F.injective_orbitMap_of_full hF).eq_iff.symm

section Equivariance

variable (R : X.NaturalRep x) (R' : Y.NaturalRep y) {V : Set Obj} (g : X.Isotropy x)

theorem src_ψ_Φ (hVU : V ⊆ R.U) (hgW : ∀ u ∈ V, R.Φ g u ∈ T.W) {u : Obj} (hu : u ∈ V) :
    Y.src (T.ψ (R.Φ g u)) = Y.tgt (F.mor (R.Γ g u)) := by
  rw [T.src_ψ _ (hgW u hu), F.tgt_mor, R.tgt_Γ g u (hVU hu)]

theorem src_comp_ψ_Φ (hVU : V ⊆ R.U) (hVW : V ⊆ T.W) (hgW : ∀ u ∈ V, R.Φ g u ∈ T.W) {u : Obj}
    (hu : u ∈ V) :
    Y.src (Y.comp (T.ψ (R.Φ g u)) (F.mor (R.Γ g u))) = Y.tgt (Y.inv (T.ψ u)) := by
  rw [Y.src_comp _ _ (T.src_ψ_Φ R g hVU hgW hu), F.src_mor, R.src_Γ g u (hVU hu), Y.tgt_inv,
    T.src_ψ u (hVW hu)]

/-- **The natural actions are intertwined by `Q`** (2021 pp. 467–469, (10.2), (10.3)): on a
preconnected `V ∋ x` inside `U(x)` and `W` with `Q(V)`, `Q(ĝ(V)) ⊆ U(y)`,
`Γ'(ψ ∘ F(g) ∘ ψ⁻¹, Q(u)) = ψ_{ĝ(u)} ∘ F(Γ(g, u)) ∘ ψ_u⁻¹`; both sides are continuous sections of
`s` over `Q` agreeing at `x`. -/
theorem Γ_conj (hVU : V ⊆ R.U) (hVW : V ⊆ T.W) (hgW : ∀ u ∈ V, R.Φ g u ∈ T.W)
    (hV : IsPreconnected V) (hxV : x ∈ V) (hQV : ∀ u ∈ V, T.Q u ∈ R'.U) :
    ∀ u ∈ V, R'.Γ (T.conj g) (T.Q u) =
      Y.comp (Y.comp (T.ψ (R.Φ g u)) (F.mor (R.Γ g u))) (Y.inv (T.ψ u)) := by
  have hcont1 : ContinuousOn (fun u => R'.Γ (T.conj g) (T.Q u)) V :=
    (R'.isScSmoothOn_Γ _).continuousOn.comp (T.continuousOn_Q.mono hVW) hQV
  have hcont2 : ContinuousOn
      (fun u => Y.comp (Y.comp (T.ψ (R.Φ g u)) (F.mor (R.Γ g u))) (Y.inv (T.ψ u))) V := by
    refine Y.continuousOn_comp_of (Y.continuousOn_comp_of ?_ ?_
      fun u hu => T.src_ψ_Φ R g hVU hgW hu) ?_ fun u hu => T.src_comp_ψ_Φ R g hVU hVW hgW hu
    · exact T.continuousOn_ψ.comp ((R.continuousOn_Φ g).mono hVU) hgW
    · exact F.continuous_mor.comp_continuousOn ((R.isScSmoothOn_Γ g).continuousOn.mono hVU)
    · exact Y.continuous_inv.comp_continuousOn (T.continuousOn_ψ.mono hVW)
  refine (T2Space.isSeparatedMap Y.src).eqOn_of_comp_eqOn Y.isLocalScDiffeo_src.isLocallyInjective
    hV hcont1 hcont2 (fun u hu => ?_) hxV ?_
  · change Y.src (R'.Γ (T.conj g) (T.Q u)) =
      Y.src (Y.comp (Y.comp (T.ψ (R.Φ g u)) (F.mor (R.Γ g u))) (Y.inv (T.ψ u)))
    rw [R'.src_Γ _ _ (hQV u hu), Y.src_comp _ _ (T.src_comp_ψ_Φ R g hVU hVW hgW hu), Y.src_inv,
      T.tgt_ψ u (hVW hu)]
  · rw [T.Q_self, R'.Γ_self, T.conj_val, R.Φ_self, R.Γ_self, T.ψ_self]

/-- **`Q(g ∗ u) = (ψ ∘ F(g) ∘ ψ⁻¹) ∗ Q(u)`** (the computation `Q(g) ∗ Q(z) = Q(g ∗ z)` of the
proof of Proposition 10.1.9). -/
theorem Q_Φ (hVU : V ⊆ R.U) (hVW : V ⊆ T.W) (hgW : ∀ u ∈ V, R.Φ g u ∈ T.W)
    (hV : IsPreconnected V) (hxV : x ∈ V) (hQV : ∀ u ∈ V, T.Q u ∈ R'.U) :
    ∀ u ∈ V, T.Q (R.Φ g u) = R'.Φ (T.conj g) (T.Q u) := fun u hu => by
  have h := congrArg Y.tgt (T.Γ_conj R R' g hVU hVW hgW hV hxV hQV u hu)
  rw [R'.tgt_Γ _ _ (hQV u hu), Y.tgt_comp _ _ (T.src_comp_ψ_Φ R g hVU hVW hgW hu),
    Y.tgt_comp _ _ (T.src_ψ_Φ R g hVU hgW hu), T.tgt_ψ _ (hgW u hu)] at h
  exact h.symm

end Equivariance

/-- `Q` intertwines the natural actions on all of `U(x)` if `U(x) ⊆ W ∩ Q⁻¹(U(y))`. -/
theorem Q_Φ_of_subset (R : X.NaturalRep x) (R' : Y.NaturalRep y)
    (hR : R.U ⊆ T.W ∩ T.Q ⁻¹' R'.U) (g : X.Isotropy x) :
    ∀ u ∈ R.U, T.Q (R.Φ g u) = R'.Φ (T.conj g) (T.Q u) :=
  T.Q_Φ R R' g subset_rfl (fun _ hu => (hR hu).1) (fun _ hu => (hR (R.mapsTo_Φ g hu)).1)
    R.isConnected_U.isPreconnected R.mem_U fun _ hu => (hR hu).2

/-- **The push-forward of a natural representation** (2021 p. 467: "if `U(x)` is small enough
the natural action on `U(y)` is defined"): for `U(x) ⊆ W ∩ Q⁻¹(U₀(y))`, the natural
representation `U₀(y)` restricts to `Q(U(x))`, and `Q` intertwines the actions. -/
theorem exists_naturalRep_push (hF : F.IsEquivalence) (R : X.NaturalRep x)
    (R'₀ : Y.NaturalRep y) (hR : R.U ⊆ T.W ∩ T.Q ⁻¹' R'₀.U) :
    ∃ R' : Y.NaturalRep y, R'.U = T.Q '' R.U ∧ R'.Φ = R'₀.Φ ∧ R'.Γ = R'₀.Γ ∧
      ∀ g, ∀ u ∈ R.U, T.Q (R.Φ g u) = R'.Φ (T.conj g) (T.Q u) := by
  have hRW : R.U ⊆ T.W := fun u hu => (hR hu).1
  have hd := T.isScDiffeoOn_image R.isOpen_U hRW
  have heq := T.Q_Φ_of_subset R R'₀ hR
  obtain ⟨R', h1, h2, h3⟩ := Y.exists_naturalRep_restrict R'₀ hd.isOpen_target
    (R.isConnected_U.image _ (T.continuousOn_Q.mono hRW)) ⟨x, R.mem_U, T.Q_self⟩
    (image_subset_iff.2 fun u hu => (hR hu).2) fun k => by
      obtain ⟨g, rfl⟩ := (T.bijective_conj hF).2 k
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨R.Φ g u, R.mapsTo_Φ g hu, heq g u hu⟩
  exact ⟨R', h1, h2, h3, fun g u hu => by rw [h2]; exact heq g u hu⟩

/-- **The pull-back of a natural representation** (2021 p. 467: "Similarly … we can pull back
the natural representation on `U(y)`"): for `U₀(x) ⊆ W ∩ Q⁻¹(U₁(y))` and a natural
representation `U(y) ⊆ Q(U₀(x))`, the natural representation `U₀(x)` restricts to
`Q⁻¹(U(y))`, and `Q` intertwines the actions. -/
theorem exists_naturalRep_pull (R₀ : X.NaturalRep x) (R'₁ : Y.NaturalRep y)
    (hR₀ : R₀.U ⊆ T.W ∩ T.Q ⁻¹' R'₁.U) (R' : Y.NaturalRep y) (hR' : R'.U ⊆ T.Q '' R₀.U) :
    ∃ R : X.NaturalRep x, R.U = R₀.U ∩ T.Q ⁻¹' R'.U ∧ T.Q '' R.U = R'.U ∧ R.Φ = R₀.Φ ∧
      R.Γ = R₀.Γ ∧ ∀ g, ∀ u ∈ R.U, T.Q (R.Φ g u) = R'.Φ (T.conj g) (T.Q u) := by
  have hR₀W : R₀.U ⊆ T.W := fun u hu => (hR₀ hu).1
  have heq₁ := T.Q_Φ_of_subset R₀ R'₁ hR₀
  have hR'R'₁ : R'.U ⊆ R'₁.U := hR'.trans (image_subset_iff.2 fun u hu => (hR₀ hu).2)
  have hΦ : ∀ k, EqOn (R'₁.Φ k) (R'.Φ k) R'.U := fun k =>
    R'₁.eqOn_Φ R' R'.isConnected_U.isPreconnected R'.mem_U hR'R'₁ subset_rfl k
  have hUo : IsOpen (R₀.U ∩ T.Q ⁻¹' R'.U) :=
    (T.continuousOn_Q.mono hR₀W).isOpen_inter_preimage R₀.isOpen_U R'.isOpen_U
  have hUimg : T.Q '' (R₀.U ∩ T.Q ⁻¹' R'.U) = R'.U := by
    refine Subset.antisymm (image_subset_iff.2 fun u hu => hu.2) fun z hz => ?_
    obtain ⟨u, hu, rfl⟩ := hR' hz
    exact ⟨u, ⟨hu, hz⟩, rfl⟩
  have hd := T.isScDiffeoOn_image hUo fun u hu => hR₀W hu.1
  rw [hUimg] at hd
  have hUc : IsConnected (R₀.U ∩ T.Q ⁻¹' R'.U) := by
    have himg : T.Qinv '' R'.U = R₀.U ∩ T.Q ⁻¹' R'.U := hd.symm.image_eq
    rw [← himg]
    exact R'.isConnected_U.image _ hd.isScSmoothOn_inv.continuousOn
  have hinv : ∀ g, MapsTo (R₀.Φ g) (R₀.U ∩ T.Q ⁻¹' R'.U) (R₀.U ∩ T.Q ⁻¹' R'.U) :=
    fun g u hu => ⟨R₀.mapsTo_Φ g hu.1, by
      rw [mem_preimage, heq₁ g u hu.1, hΦ _ hu.2]
      exact R'.mapsTo_Φ _ hu.2⟩
  obtain ⟨R, h1, h2, h3⟩ := X.exists_naturalRep_restrict R₀ hUo hUc
    ⟨R₀.mem_U, by rw [mem_preimage, T.Q_self]; exact R'.mem_U⟩ inter_subset_left hinv
  refine ⟨R, h1, h1 ▸ hUimg, h2, h3, fun g u hu => ?_⟩
  rw [h1] at hu
  rw [h2, heq₁ g u hu.1, hΦ _ hu.2]

end TransportChart

/-! ### Proposition 10.1.9 -/

/-- **2021 Proposition 10.1.9, p. 468 (new in the 2021 edition)**: if `F : X → Y` is an
equivalence, `X` has the local regularity property (Definition 7.4.19) iff `Y` has it. -/
theorem proposition_10_1_9 (hF : F.IsEquivalence) : X.IsLR ↔ Y.IsLR := by
  constructor
  · intro hX y O hO hyO
    obtain ⟨x, ψ₀, hs, ht⟩ := hF.exists_iso y
    obtain ⟨T, -⟩ := exists_transportChart hF.isLocalScDiffeo_obj hs ht
    obtain ⟨R'₀, hR'₀⟩ := Y.theorem_7_1_13 y (hO.inter T.isOpen_W') ⟨hyO, T.mem_W'⟩
    have hO' : IsOpen (T.W ∩ T.Q ⁻¹' R'₀.U) :=
      T.continuousOn_Q.isOpen_inter_preimage T.isOpen_W R'₀.isOpen_U
    obtain ⟨R, hRO', hRLR⟩ := hX x _ hO'
      ⟨T.mem_W, by rw [mem_preimage, T.Q_self]; exact R'₀.mem_U⟩
    obtain ⟨R', hR'U, -, -, hequiv⟩ := T.exists_naturalRep_push hF R R'₀ hRO'
    have hRW : R.U ⊆ T.W := fun u hu => (hRO' hu).1
    have hd := T.isScDiffeoOn_image R.isOpen_U hRW
    rw [← hR'U] at hd
    refine ⟨R', ?_, (R.hasLR_iff_of_equivariant R' hd T.conj (T.bijective_conj hF).2 hequiv
      fun a ha b hb => T.π_eq_π_iff hF.full (hRW ha) (hRW hb)).1 hRLR⟩
    rw [hR'U]
    rintro _ ⟨u, hu, rfl⟩
    exact (hR'₀ (hRO' hu).2).1
  · intro hY x O hO hxO
    obtain ⟨T, -⟩ := exists_transportChart hF.isLocalScDiffeo_obj (Y.src_unit (F.obj x))
      (Y.tgt_unit (F.obj x))
    obtain ⟨R'₁, -⟩ := Y.theorem_7_1_13 (F.obj x) isOpen_univ (mem_univ _)
    have hO' : IsOpen (O ∩ (T.W ∩ T.Q ⁻¹' R'₁.U)) :=
      hO.inter (T.continuousOn_Q.isOpen_inter_preimage T.isOpen_W R'₁.isOpen_U)
    obtain ⟨R₀, hR₀⟩ := X.theorem_7_1_13 x hO'
      ⟨hxO, T.mem_W, by rw [mem_preimage, T.Q_self]; exact R'₁.mem_U⟩
    have hR₀W : R₀.U ⊆ T.W := fun u hu => (hR₀ hu).2.1
    have hd₀ := T.isScDiffeoOn_image R₀.isOpen_U hR₀W
    obtain ⟨R', hR'U, hR'LR⟩ := hY (F.obj x) _ hd₀.isOpen_target ⟨x, R₀.mem_U, T.Q_self⟩
    obtain ⟨R, hRU, hRimg, -, -, hequiv⟩ :=
      T.exists_naturalRep_pull R₀ R'₁ (fun u hu => (hR₀ hu).2) R' hR'U
    have hRW : R.U ⊆ T.W := by rw [hRU]; exact fun u hu => hR₀W hu.1
    have hd := T.isScDiffeoOn_image R.isOpen_U hRW
    rw [hRimg] at hd
    refine ⟨R, by rw [hRU]; exact fun u hu => (hR₀ hu.1).1,
      (R.hasLR_iff_of_equivariant R' hd T.conj (T.bijective_conj hF).2 hequiv
        fun a ha b hb => T.π_eq_π_iff hF.full (hRW ha) (hRW hb)).2 hR'LR⟩

/-! ### Proposition 10.1.10 -/

/-- **2021 Proposition 10.1.10 (1), p. 470 (2017: Proposition 10.4 (1), p. 340)**: if `X` has
(LR) and `F, G : X → Y` are equivalences with `|F| = |G|`, every `x` has (arbitrarily small)
natural representations `U(x)` with an sc-smooth `U(x) → 𝐘`, `z ↦ α_z : F(z) → G(z)`. -/
theorem proposition_10_1_10_one {F G : EpFunctor X Y} (hF : F.IsEquivalence)
    (hG : G.IsEquivalence) (hFG : F.orbitMap = G.orbitMap) (hX : X.IsLR) (x : Obj)
    {O : Set Obj} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ R : X.NaturalRep x, R.U ⊆ O ∧ ∃ α : Obj → Mor', X.PObj.IsScSmoothOn Y.PMor α R.U ∧
      ∀ z ∈ R.U, Y.src (α z) = F.obj z ∧ Y.tgt (α z) = G.obj z := by
  have hπ : ∀ z, Y.π (F.obj z) = Y.π (G.obj z) := fun z => by
    rw [← F.orbitMap_π, ← G.orbitMap_π, hFG]
  obtain ⟨ψ₀, hs, ht⟩ := Y.π_eq_π_iff.1 (hπ x)
  obtain ⟨T, -⟩ := exists_transportChart hF.isLocalScDiffeo_obj hs ht
  obtain ⟨WG, WG', Ginv, hxWG, hdG⟩ := hG.isLocalScDiffeo_obj x
  -- `β = G⁻¹ ∘ Q` on `W₁ = W ∩ Q⁻¹(G(WG))`, the composition (10.4)
  have hW₁o : IsOpen (T.W ∩ T.Q ⁻¹' WG') :=
    T.continuousOn_Q.isOpen_inter_preimage T.isOpen_W hdG.isOpen_target
  have hd1 := T.isScDiffeoOn_image hW₁o inter_subset_left
  have hd2 := hdG.symm.restrict hd1.isOpen_target (image_subset_iff.2 fun u hu => hu.2)
  have hβ := hd2.comp hd1
  obtain ⟨R, hRO, hRLR⟩ := hX x _ (hO.inter hW₁o)
    ⟨hxO, T.mem_W, by rw [mem_preimage, T.Q_self]; exact hdG.mapsTo hxWG⟩
  have hRW₁ : R.U ⊆ T.W ∩ T.Q ⁻¹' WG' := fun u hu => (hRO hu).2
  have hβR := hβ.restrict R.isOpen_U hRW₁
  have e := hβR.image_eq
  rw [← e] at hβR
  have hβx : (Ginv ∘ T.Q) x = x := by
    rw [Function.comp_apply, T.Q_self, hdG.left_inv x hxWG]
  have hβπ : ∀ z ∈ R.U, X.π ((Ginv ∘ T.Q) z) = X.π z := by
    intro z hz
    have hzW₁ := hRW₁ hz
    apply G.injective_orbitMap_of_full hG.full
    rw [G.orbitMap_π, G.orbitMap_π, Function.comp_apply, hdG.right_inv _ hzW₁.2, T.π_Q hzW₁.1,
      hπ z]
  -- Lemma 7.4.20: `β(U(x)) = U(x)`; then (LR) gives `β = ĝ`
  obtain ⟨-, hβRR⟩ := X.lemma_7_4_20 R hβR hβx hβπ
  obtain ⟨g, hg⟩ := hRLR _ _ hβRR hβπ
  -- `α_z = G(Γ(g, z))⁻¹ ∘ ψ_z`
  have hc : ∀ z ∈ R.U, Y.src (Y.inv (G.mor (R.Γ g z))) = Y.tgt (T.ψ z) := fun z hz => by
    rw [Y.src_inv, G.tgt_mor, R.tgt_Γ g z hz, ← hg z hz, Function.comp_apply,
      hdG.right_inv _ (hRW₁ hz).2, T.tgt_ψ z (hRW₁ hz).1]
  refine ⟨R, fun u hu => (hRO hu).1, fun z => Y.comp (Y.inv (G.mor (R.Γ g z))) (T.ψ z), ?_,
    fun z hz => ⟨?_, ?_⟩⟩
  · refine Y.isScSmoothOn_comp_of ?_ (T.isScSmoothOn_ψ.mono R.isOpen_U fun u hu => (hRW₁ hu).1) hc
    exact MPolyfold.IsScSmoothOn.comp Y.isScSmoothMap_inv
      (MPolyfold.IsScSmoothOn.comp G.isScSmoothMap_mor (R.isScSmoothOn_Γ g) (mapsTo_univ _ _))
      (mapsTo_univ _ _)
  · rw [Y.src_comp _ _ (hc z hz), T.src_ψ z (hRW₁ hz).1]
  · rw [Y.tgt_comp _ _ (hc z hz), Y.tgt_inv, G.src_mor, R.src_Γ g z hz]

/-- **2021 Proposition 10.1.10 (2), p. 470 (2017: Proposition 10.4 (2), p. 340)**: under the
hypotheses of (1), the tangent functors satisfy `|TF| = |TG|`: for `v ∈ T_zX` the vector
`Tα(v)` is a morphism `TF(v) → TG(v)` of `TY`. -/
theorem proposition_10_1_10_two {F G : EpFunctor X Y} (hF : F.IsEquivalence)
    (hG : G.IsEquivalence) (hFG : F.orbitMap = G.orbitMap) (hX : X.IsLR) :
    F.tangent.orbitMap = G.tangent.orbitMap := by
  funext q
  induction q using Quotient.inductionOn with | h v => ?_
  change F.tangent.orbitMap (X.tangentEpGroupoid.π v) = G.tangent.orbitMap
    (X.tangentEpGroupoid.π v)
  rw [F.tangent.orbitMap_π, G.tangent.orbitMap_π]
  obtain ⟨R, -, α, hα, hαFG⟩ := proposition_10_1_10_one hF hG hFG hX
    (X.PObj.levelVal 1 (X.PObj.tangentProj v)) isOpen_univ (mem_univ _)
  have hv : v ∈ X.PObj.tangentPreimage R.U := R.mem_U
  refine (GroupoidStr.π_eq_π_iff _).2 ⟨MPolyfold.tangentMapOn hα v, ?_, ?_⟩
  · exact MPolyfold.tangentMap_tangentMapOn_of_eqOn hα Y.isScSmoothMap_src F.isScSmoothMap_obj
      (fun z hz => (hαFG z hz).1) hv
  · exact MPolyfold.tangentMap_tangentMapOn_of_eqOn hα Y.isScSmoothMap_tgt G.isScSmoothMap_obj
      (fun z hz => (hαFG z hz).2) hv

/-- **Proposition 10.1.10 (1)** with (LR) for `Y` in place of `X` (Proposition 10.1.9). -/
theorem proposition_10_1_10_one_of_isLR_right {F G : EpFunctor X Y} (hF : F.IsEquivalence)
    (hG : G.IsEquivalence) (hFG : F.orbitMap = G.orbitMap) (hY : Y.IsLR) (x : Obj)
    {O : Set Obj} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ R : X.NaturalRep x, R.U ⊆ O ∧ ∃ α : Obj → Mor', X.PObj.IsScSmoothOn Y.PMor α R.U ∧
      ∀ z ∈ R.U, Y.src (α z) = F.obj z ∧ Y.tgt (α z) = G.obj z :=
  proposition_10_1_10_one hF hG hFG ((proposition_10_1_9 hF).2 hY) x hO hxO

/-- **Witness** for `TransportChart`: along an equivalence, every `x` has a chart along the unit
`1_{F(x)}`. -/
theorem TransportChart.nonempty (hF : F.IsEquivalence) (x : Obj) :
    Nonempty (F.TransportChart x (F.obj x)) :=
  let ⟨T, _⟩ := exists_transportChart hF.isLocalScDiffeo_obj (Y.src_unit (F.obj x))
    (Y.tgt_unit (F.obj x))
  ⟨T⟩

end EpFunctor

end Transport

/-! ### Proposition 10.1.19 -/

/-- **2021 Proposition 10.1.19, p. 477 (new in the 2021 edition)**: if `F : X → Y` is an
equivalence, `X` has the strong local regularity property (SLR) iff `Y` has it (Proposition
10.1.9 for the lifts `Fⁱ : Xⁱ → Yⁱ`). -/
theorem EP.proposition_10_1_19 {A B : EP.{u}} {F : EpFunctor A.X B.X} (hF : F.IsEquivalence) :
    A.IsSLR ↔ B.IsSLR :=
  EP.isSLR_iff_of_isLR_iff hF fun _ _ hG => EpFunctor.proposition_10_1_9 hG

/-! ### Witnesses -/

namespace EquivalenceLRExamples

open EpGroupoid.Examples

/-- **Witness**: transport charts exist for the identity of the point ep-groupoid. -/
theorem nonempty_transportChart_pointEP (x : pointEP.Obj) :
    Nonempty ((EpFunctor.id pointEP.X).TransportChart x x) :=
  EpFunctor.TransportChart.nonempty (EpFunctor.IsEquivalence.id _) x

/-- **Witness**: every object of the point ep-groupoid has a natural representation with the
property of (LR) (`NaturalRep.HasLR`). -/
theorem exists_hasLR_pointEP (x : pointEP.Obj) : ∃ R : pointEP.X.NaturalRep x, R.HasLR :=
  let ⟨R, _, h⟩ := isSLR_pointEP 0 x univ isOpen_univ (mem_univ x)
  ⟨R, h⟩

/-- **Witness** for Proposition 10.1.10: the identity functor of the point ep-groupoid satisfies
its hypotheses (`F = G = 1`, both equivalences, `|F| = |G|`, (LR)). -/
theorem proposition_10_1_10_hypotheses :
    (EpFunctor.id pointEP.X).IsEquivalence ∧ (EpFunctor.id pointEP.X).IsEquivalence ∧
      (EpFunctor.id pointEP.X).orbitMap = (EpFunctor.id pointEP.X).orbitMap ∧
      pointEP.X.IsLR :=
  ⟨EpFunctor.IsEquivalence.id _, EpFunctor.IsEquivalence.id _, rfl, isSLR_pointEP 0⟩

end EquivalenceLRExamples

end Polyfold
