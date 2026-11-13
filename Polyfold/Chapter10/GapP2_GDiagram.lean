import Polyfold.Chapter10.GapP2_GBundleLR

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.5 (pp. 504–506; 2017: pp. 364–366): **the diagram (10.24) with
generalized vertical maps**, and **the local expressions `q`, `Q` of (10.25)**.  Numbers and pages
are the 2021 text's.

# The symbolic diagram (10.24) and its local expressions

## The text, paraphrased

(p. 504) A generalized strong bundle map `[D] : W → W'` covers `[d] : X → X'`; the square (10.24)
with vertical arrows `P`, `P'` "does not make too much sense", but with the vertical arrows
replaced by "a suitable generalized map version" it commutes (left to the reader).  (p. 505) For
`x`, `x'` with `|[d]|(|x|) = |x'|`, a representative `X ←φ X'' →ψ X'`, `x''` and morphisms
`a : φ(x'') → x`, `b : ψ(x'') → x'` give `γ : G_x → G'_{x'}` and an equivariant sc-smooth germ
`q : O(X, x) → O(X', x')`, `q(g ∗ z) = γ(g) ∗ q(z)`, the composite
`U(x) ← U(φ(x'')) ← U(x'') → U(ψ(x'')) → U(x')` of `t ∘ (s|U(a))⁻¹`, of `φ⁻¹`, of `ψ` and of
`t ∘ (s|U(b))⁻¹`.  (p. 506) `q` has a natural strong bundle lift `Q` with `P' ∘ Q = q ∘ P`, (10.25);
both depend on the representative.

## What is formalized

* `SEP.projEP` (`P : (W, 𝐖) → X` as a morphism of `EP`), `SEP.projEP_comp` (`P' ∘ Ψ = ψ ∘ P''`).
* **`SBLocalization.SDiagram.square_10_24`**, **`GenSBMap.square_10_24`**: with the vertical
  arrows the generalized maps `i(P)`, `i(P')` (`EPLoc.localizationFunctor`, Theorem 10.3.14), the
  square (10.24) commutes in `EP(E⁻¹)`: `[D]_total ≫ i(P') = i(P) ≫ [d]`.
* `EpFunctor.mor_Γ`, `obj_Φ`: an sc-smooth functor intertwines natural representations at `u` and
  `F(u)` along `F : G_u → G_{F(u)}` (both sides are sections of `s` agreeing at `u`).
* **`EPLocalization.Diagram.exists_germ_q`**: the germ `q` of p. 505 for the data
  `(x'', a, b)`: natural representations `U(x)`, `U(x')` and an sc-smooth `q : U(x) → U(x')`,
  `q(x) = x'`, with `q(g ∗ z) = γ(g) ∗ q(z)` for the homomorphism `γ = Diagram.isotropyHom` of the
  same data, and `q = (t ∘ (s|U(b))⁻¹) ∘ ψ ∘ φ⁻¹ ∘ (t ∘ (s|U(a))⁻¹)⁻¹` on `U(x)`.

## The choices made

* The text's "suitable generalized map version" of `P : W → X` is `i(P) = [W ←1 W →P X]`.  The
  orbit-space square `|D|` is `GenSBMap.orbitMap_square` (`StrongBundleLocalization.lean`).
* The germ is stated on natural representations: `U(x)` and `U(x')` carry the natural actions in
  which `q(g ∗ z) = γ(g) ∗ q(z)` is read.  The lift `Q` is in `GapP2_GDiagramLift.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### (10.24) with generalized vertical maps -/

namespace SEP

/-- **The projection `P : (W, 𝐖) → X`** of a strong bundle over an ep-groupoid, as a morphism of
`EP` from the total space to the base. -/
def projEP (A : SEP.{u}) : A.totalEP ⟶ A.baseEP :=
  A.E.projFunctor

/-- `P' ∘ Ψ = ψ ∘ P` for a strong bundle functor `Ψ` covering `ψ`. -/
theorem projEP_comp {A A' : SEP.{u}} (F : A ⟶ A') :
    (Hom.Φ F : A.totalEP ⟶ A'.totalEP) ≫ projEP A' =
      projEP A ≫ (Hom.ϕ F : A.baseEP ⟶ A'.baseEP) :=
  (Hom.isStrongBundleFunctor F).projFunctor_comp

end SEP

namespace SBLocalization

open EPLocalization

variable {A A' : SEP.{u}}

/-- **The square (10.24) with generalized vertical maps commutes** (2021 p. 505, "we leave it to
the reader"): for a diagram `D : W ←Φ W'' →Ψ W'` covering `d : X ←φ X'' →ψ X'`,
`[D] ≫ i(P') = i(P) ≫ [d]` in `EP(E⁻¹)`, with `i(P) = [W ←1 W →P X]`.  Proof: `[D] = i(Φ)⁻¹ ≫ i(Ψ)`,
`[d] = i(φ)⁻¹ ≫ i(ψ)` (`EPLoc.homMk_eq`), and `P' ∘ Ψ = ψ ∘ P''`, `P ∘ Φ = φ ∘ P''`. -/
theorem SDiagram.square_10_24 (D : SDiagram A A') :
    EPLoc.homMk D.total ≫ EPLoc.localizationFunctor.map (SEP.projEP A') =
      EPLoc.localizationFunctor.map (SEP.projEP A) ≫ EPLoc.homMk D.base := by
  set i := EPLoc.localizationFunctor.{u}
  let Φt : D.B.totalEP ⟶ A.totalEP := SEP.Hom.Φ D.Φ
  let Ψt : D.B.totalEP ⟶ A'.totalEP := SEP.Hom.Φ D.Ψ
  let φb : D.B.baseEP ⟶ A.baseEP := SEP.Hom.ϕ D.Φ
  let ψb : D.B.baseEP ⟶ A'.baseEP := SEP.Hom.ϕ D.Ψ
  have : IsIso (i.map Φt) := EPLoc.isInvertedBy_localizationFunctor Φt D.hΦ.isEquivalence
  have : IsIso (i.map φb) := EPLoc.isInvertedBy_localizationFunctor φb D.hΦ.isEquivalence_base
  have h1 : EPLoc.homMk D.total = inv (i.map Φt) ≫ i.map Ψt := EPLoc.homMk_eq D.total
  have h2 : EPLoc.homMk D.base = inv (i.map φb) ≫ i.map ψb := EPLoc.homMk_eq D.base
  rw [h1, h2]
  have hΨ : i.map Ψt ≫ i.map (SEP.projEP A') = i.map (SEP.projEP D.B) ≫ i.map ψb := by
    rw [← i.map_comp, ← i.map_comp]
    exact congrArg i.map (SEP.projEP_comp D.Ψ)
  have hΦ : i.map Φt ≫ i.map (SEP.projEP A) = i.map (SEP.projEP D.B) ≫ i.map φb := by
    rw [← i.map_comp, ← i.map_comp]
    exact congrArg i.map (SEP.projEP_comp D.Φ)
  have hΦ' : inv (i.map Φt) ≫ i.map (SEP.projEP D.B) = i.map (SEP.projEP A) ≫ inv (i.map φb) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hΦ, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  calc (inv (i.map Φt) ≫ i.map Ψt) ≫ i.map (SEP.projEP A')
      = inv (i.map Φt) ≫ (i.map Ψt ≫ i.map (SEP.projEP A')) := Category.assoc _ _ _
    _ = inv (i.map Φt) ≫ (i.map (SEP.projEP D.B) ≫ i.map ψb) := by rw [hΨ]
    _ = (inv (i.map Φt) ≫ i.map (SEP.projEP D.B)) ≫ i.map ψb := (Category.assoc _ _ _).symm
    _ = (i.map (SEP.projEP A) ≫ inv (i.map φb)) ≫ i.map ψb := by rw [hΦ']
    _ = i.map (SEP.projEP A) ≫ (inv (i.map φb) ≫ i.map ψb) := Category.assoc _ _ _

/-- **The square (10.24) with generalized vertical maps commutes**, on classes:
`[D] ≫ i(P') = i(P) ≫ [d]` in `EP(E⁻¹)` for every generalized strong bundle map `[D]`. -/
theorem GenSBMap.square_10_24 (f : GenSBMap A A') :
    f.total ≫ EPLoc.localizationFunctor.map (SEP.projEP A') =
      EPLoc.localizationFunctor.map (SEP.projEP A) ≫ f.base :=
  Quot.inductionOn (motive := fun f : GenSBMap A A' =>
    f.total ≫ EPLoc.localizationFunctor.map (SEP.projEP A') =
      EPLoc.localizationFunctor.map (SEP.projEP A) ≫ f.base) f
    fun D => D.square_10_24

end SBLocalization

/-! ### Sc-smooth functors and natural representations -/

namespace EpFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {Y : EpGroupoid Obj' Mor'}
  (F : EpFunctor X Y) {u : Obj} (R : X.NaturalRep u) (R' : Y.NaturalRep (F.obj u))
  {V : Set Obj} (hVU : V ⊆ R.U) (hV : IsPreconnected V) (huV : u ∈ V)
  (hFV : ∀ v ∈ V, F.obj v ∈ R'.U) (k : X.Isotropy u)
include hVU hV huV hFV

/-- **An sc-smooth functor intertwines the maps `Γ`**: `F(Γ(k, v)) = Γ'(F(k), F(v))` on a
preconnected `V ∋ u` inside `U(u)` with `F(V) ⊆ U'(F(u))` (both are continuous sections of `s`
over `F` agreeing at `u`). -/
theorem mor_Γ : ∀ v ∈ V, F.mor (R.Γ k v) = R'.Γ (F.isotropyHom u k) (F.obj v) := by
  have hc1 : ContinuousOn (fun v => F.mor (R.Γ k v)) V :=
    F.continuous_mor.comp_continuousOn ((R.isScSmoothOn_Γ k).continuousOn.mono hVU)
  have hc2 : ContinuousOn (fun v => R'.Γ (F.isotropyHom u k) (F.obj v)) V :=
    (R'.isScSmoothOn_Γ _).continuousOn.comp F.continuous_obj'.continuousOn hFV
  refine (T2Space.isSeparatedMap Y.src).eqOn_of_comp_eqOn Y.isLocalScDiffeo_src.isLocallyInjective
    hV hc1 hc2 (fun v hv => ?_) huV ?_
  · change Y.src (F.mor (R.Γ k v)) = Y.src (R'.Γ (F.isotropyHom u k) (F.obj v))
    rw [F.src_mor, R.src_Γ k v (hVU hv), R'.src_Γ _ _ (hFV v hv)]
  · rw [R.Γ_self, R'.Γ_self, isotropyHom_val]

/-- **An sc-smooth functor is equivariant on natural representations**:
`F(k ∗ v) = F(k) ∗ F(v)` on `V`. -/
theorem obj_Φ : ∀ v ∈ V, F.obj (R.Φ k v) = R'.Φ (F.isotropyHom u k) (F.obj v) := fun v hv => by
  rw [← R.tgt_Γ k v (hVU hv), ← F.tgt_mor, F.mor_Γ R R' hVU hV huV hFV k v hv,
    R'.tgt_Γ _ _ (hFV v hv)]

end EpFunctor

/-! ### The germ `q` of p. 505 -/

namespace EPLocalization.Diagram

variable {X Y : EP.{u}} (d : Diagram X Y)

/-- **`γ` in terms of the charts**: for the charts `Q_a` along `a` (of `φ`) and `Q_b` along `b` (of
the identity), `γ(a ∘ φ(k) ∘ a⁻¹) = b ∘ ψ(k) ∘ b⁻¹`, i.e. `γ ∘ conj_a = conj_b ∘ ψ`. -/
theorem isotropyHom_conj {x : X.Obj} {x' : Y.Obj} {x'' : d.A.Obj} (a : X.Mor)
    (ha : X.X.src a = d.F.obj x'') (ha' : X.X.tgt a = x) (b : Y.Mor)
    (hb : Y.X.src b = d.Φ.obj x'') (hb' : Y.X.tgt b = x') (Ta : d.F.TransportChart x'' x)
    (hTa : Ta.ψ₀ = a) (Tb : (EpFunctor.id Y.X).TransportChart (d.Φ.obj x'') x') (hTb : Tb.ψ₀ = b)
    (k : d.A.X.Isotropy x'') :
    d.isotropyHom a ha ha' b hb hb' (Ta.conj k) = Tb.conj (d.Φ.isotropyHom x'' k) := by
  have hF := d.isEquivalence_F
  obtain ⟨k', hk'1, hk'2⟩ := d.isotropyHom_spec a ha ha' b hb hb' (Ta.conj k)
  have hk : k' = k := by
    refine (hF.bijective_isotropyHom x'').1 (GroupoidStr.Isotropy.ext ?_)
    rw [EpFunctor.isotropyHom_val, EpFunctor.isotropyHom_val, hk'1, Ta.conj_val, hTa]
    have e1 : X.X.src a = X.X.tgt (d.F.mor k.val) := by
      rw [d.F.tgt_mor, k.tgt_val, ha]
    have e3 : X.X.src (d.F.mor k.val) = X.X.src a := by
      rw [d.F.src_mor, k.src_val, ha]
    have e2 : X.X.src (X.X.comp a (d.F.mor k.val)) = X.X.tgt (X.X.inv a) := by
      rw [X.X.src_comp _ _ e1, GroupoidStr.tgt_inv, e3]
    rw [← X.X.comp_assoc _ _ _ (by rw [GroupoidStr.src_inv, X.X.tgt_comp _ _ e1]) e2,
      GroupoidStr.inv_comp_cancel_left e1,
      X.X.comp_assoc _ _ _ (by rw [GroupoidStr.tgt_inv, e3]) (X.X.src_inv a),
      X.X.inv_comp, GroupoidStr.comp_unit_of_eq e3]
  subst hk
  refine GroupoidStr.Isotropy.ext ?_
  rw [hk'2, Tb.conj_val, hTb]
  rfl

/-- **The equivariant germ `q : O(X, x) → O(X', x')`** (2021 p. 505): for a diagram
`X ←φ X'' →ψ X'`, `x''` and `a : φ(x'') → x`, `b : ψ(x'') → x'`, there are natural
representations `U(x)`, `U(x')` and an sc-smooth `q : U(x) → U(x')` with `q(x) = x'` and
`q(g ∗ z) = γ(g) ∗ q(z)`, `γ = isotropyHom a b`; `q` is the composite of the charts
`Q_a = (t ∘ (s|U(a))⁻¹) ∘ φ` (inverted) and `Q_b = t ∘ (s|U(b))⁻¹` with `ψ`
(`EpFunctor.TransportChart`). -/
theorem exists_germ_q {x : X.Obj} {x' : Y.Obj} {x'' : d.A.Obj} (a : X.Mor)
    (ha : X.X.src a = d.F.obj x'') (ha' : X.X.tgt a = x) (b : Y.Mor)
    (hb : Y.X.src b = d.Φ.obj x'') (hb' : Y.X.tgt b = x') :
    ∃ (Ta : d.F.TransportChart x'' x) (Tb : (EpFunctor.id Y.X).TransportChart (d.Φ.obj x'') x')
      (R : X.X.NaturalRep x) (R' : Y.X.NaturalRep x'),
      Ta.ψ₀ = a ∧ Tb.ψ₀ = b ∧ R.U ⊆ Ta.W' ∧ (∀ z ∈ R.U, Ta.Qinv z ∈ Ta.W) ∧
      (∀ z ∈ R.U, d.Φ.obj (Ta.Qinv z) ∈ Tb.W) ∧
      X.X.PObj.IsScSmoothOn Y.X.PObj (Tb.Q ∘ d.Φ.obj ∘ Ta.Qinv) R.U ∧
      MapsTo (Tb.Q ∘ d.Φ.obj ∘ Ta.Qinv) R.U R'.U ∧ (Tb.Q ∘ d.Φ.obj ∘ Ta.Qinv) x = x' ∧
      ∀ g : X.X.Isotropy x, ∀ z ∈ R.U, (Tb.Q ∘ d.Φ.obj ∘ Ta.Qinv) (R.Φ g z) =
        R'.Φ (d.isotropyHom a ha ha' b hb hb' g) ((Tb.Q ∘ d.Φ.obj ∘ Ta.Qinv) z) := by
  have hF := d.isEquivalence_F
  obtain ⟨Ta, hTa⟩ := EpFunctor.exists_transportChart hF.isLocalScDiffeo_obj ha ha'
  obtain ⟨Tb, hTb⟩ := EpFunctor.exists_transportChart
    (EpFunctor.IsEquivalence.id Y.X).isLocalScDiffeo_obj hb hb'
  -- natural representations at `x'`, `ψ(x'')`, `x''`, `x`
  obtain ⟨R', -⟩ := Y.X.theorem_7_1_13 x' isOpen_univ (mem_univ _)
  have hOb : IsOpen (Tb.W ∩ Tb.Q ⁻¹' R'.U) :=
    Tb.continuousOn_Q.isOpen_inter_preimage Tb.isOpen_W R'.isOpen_U
  obtain ⟨Rb, hRb⟩ := Y.X.theorem_7_1_13 (d.Φ.obj x'') hOb
    ⟨Tb.mem_W, by rw [mem_preimage, Tb.Q_self]; exact R'.mem_U⟩
  obtain ⟨Rx₀, -⟩ := X.X.theorem_7_1_13 x isOpen_univ (mem_univ _)
  have hO'' : IsOpen ((Ta.W ∩ Ta.Q ⁻¹' Rx₀.U) ∩ d.Φ.obj ⁻¹' Rb.U) :=
    (Ta.continuousOn_Q.isOpen_inter_preimage Ta.isOpen_W Rx₀.isOpen_U).inter
      (Rb.isOpen_U.preimage d.Φ.continuous_obj')
  obtain ⟨R'', hR''⟩ := d.A.X.theorem_7_1_13 x'' hO''
    ⟨⟨Ta.mem_W, by rw [mem_preimage, Ta.Q_self]; exact Rx₀.mem_U⟩, Rb.mem_U⟩
  obtain ⟨R, hRU, -, -, hRequiv⟩ := Ta.exists_naturalRep_push hF R'' Rx₀ fun v hv => (hR'' hv).1
  have hR''W : R''.U ⊆ Ta.W := fun v hv => (hR'' hv).1.1
  have hd := Ta.isScDiffeoOn_image R''.isOpen_U hR''W
  rw [← hRU] at hd
  have hQinv : ∀ z ∈ R.U, Ta.Qinv z ∈ R''.U := fun z hz => hd.mapsTo_inv hz
  have hΦb : ∀ v ∈ R''.U, d.Φ.obj v ∈ Rb.U := fun v hv => (hR'' hv).2
  have hbQ := Tb.Q_Φ_of_subset Rb R' hRb
  refine ⟨Ta, Tb, R, R', hTa, hTb, fun z hz => ?_, fun z hz => hR''W (hQinv z hz),
    fun z hz => (hRb (hΦb _ (hQinv z hz))).1, ?_, fun z hz => ?_, ?_, fun g z hz => ?_⟩
  · rw [hRU] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact Ta.isScDiffeoOn_Q.mapsTo (hR''W hv)
  · refine MPolyfold.IsScSmoothOn.comp (Tb.isScDiffeoOn_Q.isScSmoothOn) ?_
      fun z hz => (hRb (hΦb _ (hQinv z hz))).1
    exact MPolyfold.IsScSmoothOn.comp (d.Φ.isScSmoothMap_obj.mono isOpen_univ
      (subset_univ _)) hd.isScSmoothOn_inv (mapsTo_univ _ _)
  · exact (hRb (hΦb _ (hQinv z hz))).2
  · have hx : Ta.Qinv x = x'' :=
      (congrArg Ta.Qinv Ta.Q_self).symm.trans (Ta.isScDiffeoOn_Q.left_inv _ Ta.mem_W)
    simp only [Function.comp_apply, hx, Tb.Q_self]
  · -- `g = conj_a(k)`
    obtain ⟨k, rfl⟩ := (Ta.bijective_conj hF).2 g
    set v := Ta.Qinv z
    have hv : v ∈ R''.U := hQinv z hz
    have hzv : Ta.Q v = z := hd.right_inv z hz
    have h1 : Ta.Qinv (R.Φ (Ta.conj k) z) = R''.Φ k v := by
      rw [← hzv, ← hRequiv k v hv]
      exact Ta.isScDiffeoOn_Q.left_inv _ (hR''W (R''.mapsTo_Φ k hv))
    have h2 := d.Φ.obj_Φ R'' Rb subset_rfl R''.isConnected_U.isPreconnected R''.mem_U hΦb k v hv
    have h3 := hbQ (d.Φ.isotropyHom x'' k) _ (hΦb v hv)
    have hγ := d.isotropyHom_conj a ha ha' b hb hb' Ta hTa Tb hTb k
    simp only [Function.comp_apply, h1, h2, h3, hγ]
    rfl

end EPLocalization.Diagram

end Polyfold
