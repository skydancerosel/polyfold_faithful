import Polyfold.Chapter12.OrientationNaturality

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7** (2017: Theorem 12.12): the **functoriality** of the maps of
orientations under composition of strong bundle equivalences (left to the reader in the text).

For strong bundle equivalences `Φ : W → W'` (over `ϕ`) and `Ψ : W' → W''` (over `ψ`) with
`f = Φ^* f'`, `f' = Ψ^* f''`, the identification `Or^{f''}_{ψϕ(a)} ≃ Or^f_a` of `Ψ ∘ Φ` is the
composite of those of `Ψ` and `Φ`; hence `|Ψ ∘ Φ|_* = |Ψ|_* ∘ |Φ|_*` on `|O_f|` and
`|ψ ∘ ϕ| = |ψ| ∘ |ϕ|` on `|X_∞|`.

* `StrongBundle.LocalIso.transferT_mpullPt₃`, `transferK_mpullPt₃`: a chart point carried along
  `L` then `L₂` and one carried along `M` agree to first order at `b` when `L ∘ L₂ = M` near `b`
  (three-term form of `transferT_mpullPt₄`).
* `IsStrongBundleEquivalence.eT_comp`, `eK_comp`, `orEqv_comp`: the chart-level and orientation
  identifications of `Ψ ∘ Φ`.
* `pullback_comp_of`: `f = (Ψ ∘ Φ)^* f''` (Proposition 10.4.4).
* `orSpaceMap_comp`, `orbitOrMap_comp`, `smoothOrbitMap_comp`: functoriality on `O_f`, `|O_f|`
  and `|X_∞|`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v' u₁ v₁

section Compose3

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {X₁ : Type u₁} [TopologicalSpace X₁] [T2Space X₁] [ParacompactSpace X₁] {PX₁ : MPolyfold X₁}
  {Y₁ : Type v₁} [TopologicalSpace Y₁] [T2Space Y₁] [ParacompactSpace Y₁] {P₁ : Y₁ → X₁}
  [∀ x, AddCommGroup (P₁ ⁻¹' {x})] [∀ x, Module ℝ (P₁ ⁻¹' {x})] {B₁ : StrongBundle PX₁ P₁}

variable {U₁ : Set X₁} {U₁' : Set X'} {U₂ : Set X} {U₂' : Set X₁} {V : Set X} {V' : Set X'}

namespace StrongBundle.LocalIso

variable {L : LocalIso B₁ B' U₁ U₁'} {L₂ : LocalIso B B₁ U₂ U₂'} {M : LocalIso B B' V V'}
  {x : X'} {x₁ : X₁} {b : X}

/-- **A two-step and a one-step carried chart point with the same germ**: if `L ∘ L₂ = M` near
`b` (base and bundle maps), the base derivative between `M`'s carried chart point and the
two-step one is `Dr(z)`, as from a chart point to itself. -/
theorem baseDeriv_mpullPt₃ (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hx₁ : x₁ ∈ U₁)
    (hϕ₁ : L.ϕ x₁ = x) (h₂ : (L.mpullPt p h₁ hx₁ hϕ₁).c.φ.source ⊆ U₂') (hb : b ∈ U₂)
    (hϕ₂ : L₂.ϕ b = x₁) (k : p.c.φ.source ⊆ V') (hb' : b ∈ V) (hψ : M.ϕ b = x)
    (hG : ∃ N : Set X, IsOpen N ∧ b ∈ N ∧ (∀ y ∈ N, L.ϕ (L₂.ϕ y) = M.ϕ y) ∧
      ∀ w, P w ∈ N → L.Φ (L₂.Φ w) = M.Φ w) (v : p.c.φ.model.E 0) :
    (M.mpullPt p k hb' hψ).baseDeriv (L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂) v =
      p.baseDeriv p v := by
  obtain ⟨N, hNo, hbN, hNϕ, -⟩ := hG
  set a₃ := M.mpullPt p k hb' hψ with ha₃
  set a₁₂ := L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂ with ha₁₂
  obtain ⟨G, hGo, hG⟩ := a₃.c.φ.exists_isOpen_image_eq (s := N ∩ a₃.c.φ.source)
    inter_subset_right (hNo.inter a₃.c.φ.isOpen_source)
  set R' := (a₃.baseRet a₁₂).restrict hGo with hR'
  have hV₁ : R'.U ⊆ (a₃.baseRet a₁₂).U := inter_subset_left
  have hV₂ : R'.U ⊆ p.c.U := fun u hu => (a₃.baseRet_U_subset a₁₂) hu.1
  have hzG : r p.c.R (p.c.φ.model.E.toBase 1 p.z) ∈ G := by
    rw [p.r_toBase_z]
    have : a₃.c.φ b ∈ a₃.c.φ '' (N ∩ a₃.c.φ.source) := ⟨b, ⟨hbN, a₃.mem_source⟩, rfl⟩
    rw [hG] at this
    have h' : a₃.c.φ b = p.c.φ.model.E.toBase 1 p.z := a₃.toBase_z.symm
    rw [h'] at this
    exact this.2
  have hzV : p.z ∈ p.c.φ.model.E.lvlSet R'.U 1 := ⟨a₃.z_mem_baseRet a₁₂, hzG⟩
  have hr1 : IsSc1 p.c.U (r p.c.R) := (r_isScSmooth p.c.relOpen p.c.isRetraction).isSc1
  have hOO : a₃.c.φ.model.O = p.c.φ.model.O := M.transportChart_model_O p.c k
  have heq : EqOn (a₃.c.φ.transition a₁₂.c.φ ∘ a₃.baseRet a₁₂) (r p.c.R) R'.U := by
    intro u hu
    obtain ⟨y, hy, hy', hyu⟩ := a₃.exists_eq_of_mem_baseRet a₁₂ (hV₁ hu)
    have hrG : r p.c.R u ∈ a₃.c.φ.model.O ∩ G := ⟨hOO ▸ p.c.r_mem_O (hV₂ hu), hu.2⟩
    rw [← hG] at hrG
    obtain ⟨y₂, ⟨hy₂N, hy₂s⟩, hy₂u⟩ := hrG
    have hyy : y₂ = y := by
      have e : a₃.c.φ y₂ = a₃.c.φ y := hy₂u.trans hyu
      rw [← a₃.c.φ.symm_apply_apply hy₂s, ← a₃.c.φ.symm_apply_apply hy, e]
    subst hyy
    have hyu' : r p.c.R u = p.c.φ (M.ϕ y₂) := hyu
    change p.c.φ (L.ϕ (L₂.ϕ (M.g (p.c.φ.symm (r p.c.R u))))) = r p.c.R u
    rw [hyu', p.c.φ.symm_apply_apply hy.2, M.base.left_inv y₂ hy.1, hNϕ y₂ hy₂N]
  have := scDeriv_eq_of_eqOn_relOpen R'.relOpen (a₃.isSc1_transition a₁₂) hr1 hV₁ hV₂ heq hzV
  rw [p.baseDeriv_self]
  exact congrArg (fun T : p.c.φ.model.E 0 →L[ℝ] p.c.φ.model.E 0 => T v) this

/-- The fibre form of `baseDeriv_mpullPt₃`: the fibre transition is the identity on `K_z`. -/
theorem fiberMap_mpullPt₃ (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hx₁ : x₁ ∈ U₁)
    (hϕ₁ : L.ϕ x₁ = x) (h₂ : (L.mpullPt p h₁ hx₁ hϕ₁).c.φ.source ⊆ U₂') (hb : b ∈ U₂)
    (hϕ₂ : L₂.ϕ b = x₁) (k : p.c.φ.source ⊆ V') (hb' : b ∈ V) (hψ : M.ϕ b = x)
    (hG : ∃ N : Set X, IsOpen N ∧ b ∈ N ∧ (∀ y ∈ N, L.ϕ (L₂.ϕ y) = M.ϕ y) ∧
      ∀ w, P w ∈ N → L.Φ (L₂.Φ w) = M.Φ w) (κ : p.c.F 0) :
    (M.mpullPt p k hb' hψ).fiberMap (L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂) κ =
      p.fiberMap p κ := by
  obtain ⟨N, -, hbN, -, hNΦ⟩ := hG
  set w : p.c.φ.model.E 0 × p.c.F 0 :=
    (p.c.φ.model.E.toBase 1 p.z, ρ p.c.R (p.c.φ.model.E.toBase 1 p.z) κ) with hw
  have hwK : w ∈ p.c.toPartialEquiv.target := by
    rw [p.c.target_eq]; exact p.c.mem_K_ρ p.toBase_z_mem_O κ
  have hsrc := p.c.toPartialEquiv.map_target hwK
  have hPx : P' (p.c.toPartialEquiv.symm w) = x := by
    have h1 := p.c.covers _ hsrc
    rw [p.c.toPartialEquiv.right_inv hwK] at h1
    have h2 : p.c.φ.model.E.toBase 1 p.z = p.c.φ (P' (p.c.toPartialEquiv.symm w)) := h1
    rw [p.c.source_eq] at hsrc
    rw [p.toBase_z] at h2
    rw [← p.c.φ.symm_apply_apply hsrc, ← h2, p.c.φ.symm_apply_apply p.mem_source]
  have hV' : P' (p.c.toPartialEquiv.symm w) ∈ V' := by rw [hPx]; exact k p.mem_source
  have hPb : P (M.Ψ (p.c.toPartialEquiv.symm w)) ∈ N := by
    rw [M.covers_inv _ hV', hPx, ← hψ, M.base.left_inv _ hb']; exact hbN
  change (p.c (L.Φ (L₂.Φ (M.Ψ (p.c.toPartialEquiv.symm w))))).2 =
    (p.c (p.c.toPartialEquiv.symm w)).2
  rw [hNΦ _ hPb, M.zero.right_inv _ hV']

/-- The identification of `T_bX` between the two carried chart points is the identity. -/
theorem transferT_mpullPt₃ (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hx₁ : x₁ ∈ U₁)
    (hϕ₁ : L.ϕ x₁ = x) (h₂ : (L.mpullPt p h₁ hx₁ hϕ₁).c.φ.source ⊆ U₂') (hb : b ∈ U₂)
    (hϕ₂ : L₂.ϕ b = x₁) (k : p.c.φ.source ⊆ V') (hb' : b ∈ V) (hψ : M.ϕ b = x)
    (hG : ∃ N : Set X, IsOpen N ∧ b ∈ N ∧ (∀ y ∈ N, L.ϕ (L₂.ϕ y) = M.ϕ y) ∧
      ∀ w, P w ∈ N → L.Φ (L₂.Φ w) = M.Φ w) (v : ↥p.T) :
    (Subtype.val ((M.mpullPt p k hb' hψ).transferT
      (L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂) v) : p.c.φ.model.E 0) = v :=
  (baseDeriv_mpullPt₃ p h₁ hx₁ hϕ₁ h₂ hb hϕ₂ k hb' hψ hG v).trans
    (congrArg Subtype.val (p.transferT_self_apply v))

/-- The identification of `Y_b` between the two carried chart points is the identity. -/
theorem transferK_mpullPt₃ (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hx₁ : x₁ ∈ U₁)
    (hϕ₁ : L.ϕ x₁ = x) (h₂ : (L.mpullPt p h₁ hx₁ hϕ₁).c.φ.source ⊆ U₂') (hb : b ∈ U₂)
    (hϕ₂ : L₂.ϕ b = x₁) (k : p.c.φ.source ⊆ V') (hb' : b ∈ V) (hψ : M.ϕ b = x)
    (hG : ∃ N : Set X, IsOpen N ∧ b ∈ N ∧ (∀ y ∈ N, L.ϕ (L₂.ϕ y) = M.ϕ y) ∧
      ∀ w, P w ∈ N → L.Φ (L₂.Φ w) = M.Φ w) (κ : ↥p.K) :
    (Subtype.val ((M.mpullPt p k hb' hψ).transferK
      (L₂.mpullPt (L.mpullPt p h₁ hx₁ hϕ₁) h₂ hb hϕ₂) κ) : p.c.F 0) = κ :=
  (fiberMap_mpullPt₃ p h₁ hx₁ hϕ₁ h₂ hb hϕ₂ k hb' hψ hG κ).trans
    (congrArg Subtype.val (p.transferK_self_apply κ))

end StrongBundle.LocalIso

end Compose3

section EquivComp

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {Obj'' Mor'' : Type u} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor''] {X'' : EpGroupoid Obj'' Mor''}
  {W'' : Type u} [TopologicalSpace W''] [T2Space W''] [ParacompactSpace W''] {P'' : W'' → Obj''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
  {B'' : StrongBundle X''.PObj P''} [ParacompactSpace (pullbackSpace P'' X''.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {E'' : EpStrongBundle X'' B''}
namespace EpStrongBundle.IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  {ψ : EpFunctor X' X''} {Ψ : EpFunctor E'.toEpGroupoid E''.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ) (h' : E'.IsStrongBundleEquivalence E'' ψ Ψ)

/-! ### The chart-level maps of `Ψ ∘ Φ` -/

/-- The open set at `ψ(ϕ(a))` used to compare the local isomorphisms of `Ψ ∘ Φ` with those of
`Ψ` and `Φ`: inside `U''(a)` of `Ψ ∘ Φ`, inside `U''(ϕ(a))` of `Ψ` and inside the preimage of
`U'(a)` of `Φ`. -/
def compLocSet (a : Obj) : Set Obj'' :=
  (h'.comp h).locSet' a ∩
    (h'.locSet' (ϕ.obj a) ∩ (h'.locIso (ϕ.obj a)).g ⁻¹' h.locSet' a)

theorem isOpen_compLocSet (a : Obj) : IsOpen (compLocSet h h' a) :=
  ((h'.comp h).isOpen_locSet' a).inter
    ((h'.locIso (ϕ.obj a)).base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage
      (h'.isOpen_locSet' _) (h.isOpen_locSet' a))

theorem mem_compLocSet (a : Obj) : ψ.obj (ϕ.obj a) ∈ compLocSet h h' a := by
  refine ⟨(h'.comp h).obj_mem_locSet' a, h'.obj_mem_locSet' (ϕ.obj a), ?_⟩
  change (h'.locIso (ϕ.obj a)).g ((h'.locIso (ϕ.obj a)).ϕ (ϕ.obj a)) ∈ h.locSet' a
  rw [(h'.locIso (ϕ.obj a)).base.left_inv _ (h'.mem_locSet _)]
  exact h.obj_mem_locSet' a

/-- Near `a`, the local isomorphism of `Ψ ∘ Φ` is the composite of those of `Ψ` and `Φ`. -/
theorem germ_comp (a : Obj) :
    ∃ N : Set Obj, IsOpen N ∧ a ∈ N ∧
      (∀ y ∈ N, (h'.locIso (ϕ.obj a)).ϕ ((h.locIso a).ϕ y) = ((h'.comp h).locIso a).ϕ y) ∧
      ∀ w, P w ∈ N → (h'.locIso (ϕ.obj a)).Φ ((h.locIso a).Φ w) = ((h'.comp h).locIso a).Φ w :=
  ⟨univ, isOpen_univ, mem_univ a, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **`eT` of `Ψ ∘ Φ` is `eT` of `Φ` after `eT` of `Ψ`**: `T_{ψϕ(a)}X'' → T_{ϕ(a)}X' → T_aX`. -/
theorem eT_comp {a : Obj} (hs : a ∈ X.PObj.smoothSet)
    (v : ↥(orPt B'' (ψ.obj (ϕ.obj a)) (h'.smooth_obj (h.smooth_obj hs))).T) :
    (h'.comp h).eT a hs v = h.eT a hs (h'.eT (ϕ.obj a) (h.smooth_obj hs) v) := by
  set p := restrPt B'' (ψ.obj (ϕ.obj a)) (isOpen_compLocSet h h' a) (mem_compLocSet h h' a)
    (h'.smooth_obj (h.smooth_obj hs)) with hp
  have hpV : p.c.φ.source ⊆ compLocSet h h' a := restrPt_sub _ _ _ _
  have hpc : p.c.φ.source ⊆ (h'.comp h).locSet' a := fun y hy => (hpV hy).1
  have hp' : p.c.φ.source ⊆ h'.locSet' (ϕ.obj a) := fun y hy => (hpV hy).2.1
  set r := (h'.locIso (ϕ.obj a)).mpullPt p hp' (h'.mem_locSet (ϕ.obj a)) rfl with hr
  have hrs : r.c.φ.source ⊆ h.locSet' a := by
    rintro y ⟨hyU, hyp⟩
    have := (hpV hyp).2.2
    change (h'.locIso (ϕ.obj a)).g ((h'.locIso (ϕ.obj a)).ϕ y) ∈ h.locSet' a at this
    rwa [(h'.locIso (ϕ.obj a)).base.left_inv y hyU] at this
  set A := (h.locIso a).mpullPt r hrs (h.mem_locSet a) rfl with hA
  set C := ((h'.comp h).locIso a).mpullPt p hpc ((h'.comp h).mem_locSet a) rfl with hC
  set t := (orPt B'' (ψ.obj (ϕ.obj a)) (h'.smooth_obj (h.smooth_obj hs))).transferT p v
  have e1 : (h'.comp h).eT a hs v = C.transferT (orPt B a hs) t := by
    exact ((h'.comp h).eT_eq hs p hpc v).trans rfl
  have e2 : h.eT a hs (h'.eT (ϕ.obj a) (h.smooth_obj hs) v) = A.transferT (orPt B a hs) t := by
    rw [h'.eT_eq (h.smooth_obj hs) p hp', h.eT_eq hs r hrs]
    exact congrArg (A.transferT (orPt B a hs))
      ((r.transferT_trans_apply (orPt B' (ϕ.obj a) (h.smooth_obj hs)) r t).trans
        (r.transferT_self_apply t))
  have h4 := StrongBundle.LocalIso.transferT_mpullPt₃ (L := h'.locIso (ϕ.obj a))
    (L₂ := h.locIso a) (M := (h'.comp h).locIso a) p hp' (h'.mem_locSet (ϕ.obj a)) rfl hrs
    (h.mem_locSet a) rfl hpc ((h'.comp h).mem_locSet a) rfl (germ_comp h h' a) t
  have e3 : A.transferT (orPt B a hs) t = C.transferT (orPt B a hs) t :=
    (congrArg (A.transferT (orPt B a hs)) (Subtype.ext h4).symm).trans
      (ChartPoint.transferT_trans_apply C A (orPt B a hs) t)
  exact e1.trans (e3.symm.trans e2.symm)

/-- **`eK` of `Ψ ∘ Φ` is `eK` of `Φ` after `eK` of `Ψ`.** -/
theorem eK_comp {a : Obj} (hs : a ∈ X.PObj.smoothSet)
    (κ : ↥(orPt B'' (ψ.obj (ϕ.obj a)) (h'.smooth_obj (h.smooth_obj hs))).K) :
    (h'.comp h).eK a hs κ = h.eK a hs (h'.eK (ϕ.obj a) (h.smooth_obj hs) κ) := by
  set p := restrPt B'' (ψ.obj (ϕ.obj a)) (isOpen_compLocSet h h' a) (mem_compLocSet h h' a)
    (h'.smooth_obj (h.smooth_obj hs)) with hp
  have hpV : p.c.φ.source ⊆ compLocSet h h' a := restrPt_sub _ _ _ _
  have hpc : p.c.φ.source ⊆ (h'.comp h).locSet' a := fun y hy => (hpV hy).1
  have hp' : p.c.φ.source ⊆ h'.locSet' (ϕ.obj a) := fun y hy => (hpV hy).2.1
  set r := (h'.locIso (ϕ.obj a)).mpullPt p hp' (h'.mem_locSet (ϕ.obj a)) rfl with hr
  have hrs : r.c.φ.source ⊆ h.locSet' a := by
    rintro y ⟨hyU, hyp⟩
    have := (hpV hyp).2.2
    change (h'.locIso (ϕ.obj a)).g ((h'.locIso (ϕ.obj a)).ϕ y) ∈ h.locSet' a at this
    rwa [(h'.locIso (ϕ.obj a)).base.left_inv y hyU] at this
  set A := (h.locIso a).mpullPt r hrs (h.mem_locSet a) rfl with hA
  set C := ((h'.comp h).locIso a).mpullPt p hpc ((h'.comp h).mem_locSet a) rfl with hC
  set t := (orPt B'' (ψ.obj (ϕ.obj a)) (h'.smooth_obj (h.smooth_obj hs))).transferK p κ
  have e1 : (h'.comp h).eK a hs κ = C.transferK (orPt B a hs) t := by
    exact ((h'.comp h).eK_eq hs p hpc κ).trans rfl
  have e2 : h.eK a hs (h'.eK (ϕ.obj a) (h.smooth_obj hs) κ) = A.transferK (orPt B a hs) t := by
    rw [h'.eK_eq (h.smooth_obj hs) p hp', h.eK_eq hs r hrs]
    exact congrArg (A.transferK (orPt B a hs))
      ((r.transferK_trans_apply (orPt B' (ϕ.obj a) (h.smooth_obj hs)) r t).trans
        (r.transferK_self_apply t))
  have h4 := StrongBundle.LocalIso.transferK_mpullPt₃ (L := h'.locIso (ϕ.obj a))
    (L₂ := h.locIso a) (M := (h'.comp h).locIso a) p hp' (h'.mem_locSet (ϕ.obj a)) rfl hrs
    (h.mem_locSet a) rfl hpc ((h'.comp h).mem_locSet a) rfl (germ_comp h h' a) t
  have e3 : A.transferK (orPt B a hs) t = C.transferK (orPt B a hs) t :=
    (congrArg (A.transferK (orPt B a hs)) (Subtype.ext h4).symm).trans
      (ChartPoint.transferK_trans_apply C A (orPt B a hs) t)
  exact e1.trans (e3.symm.trans e2.symm)

/-! ### Orientations -/

section Or

variable {f : Obj → W} {f' : Obj' → W'} {f'' : Obj'' → W''}
  (hF : E.IsScFredholmSectionFunctor f) (hF' : E'.IsScFredholmSectionFunctor f')
  (hF'' : E''.IsScFredholmSectionFunctor f'') (hpb : f = h.pullback f')
  (hpb' : f' = h'.pullback f'') (hsec : B.HasScPlusSectionsThrough)
  (hsec' : B'.HasScPlusSectionsThrough) (hsec'' : B''.HasScPlusSectionsThrough)

include hF'' hpb hpb' in
/-- `f = (Ψ ∘ Φ)^* f''` (Proposition 10.4.4). -/
theorem pullback_comp_of : f = (h'.comp h).pullback f'' := by
  rw [hpb, hpb']
  exact ((proposition_10_4_4 h h').1 f'' hF''.2.isScSmooth.1).symm

/-- **Theorem 12.5.7, functoriality at a point**: the identification
`Or^{f''}_{ψϕ(a)} ≃ Or^f_a` of `Ψ ∘ Φ` is that of `Φ` after that of `Ψ`. -/
theorem orEqv_comp (a : Obj) (hs : a ∈ X.PObj.smoothSet)
    (o : Orx f'' hF''.2 (ψ.obj (ϕ.obj a)) (h'.smooth_obj (h.smooth_obj hs))) :
    (h'.comp h).orEqv hF hF'' (pullback_comp_of h h' hF'' hpb hpb') hsec hsec'' a hs o =
      h.orEqv hF hF' hpb hsec hsec' a hs
        (h'.orEqv hF' hF'' hpb' hsec' hsec'' (ϕ.obj a) (h.smooth_obj hs) o) := by
  have m1 := h'.eT_mem hF' hF'' hpb' hsec' hsec'' (h.smooth_obj hs)
  have m2 := h.eT_mem hF hF' hpb hsec hsec' hs
  refine ((h'.comp h).orEqv_apply hF hF'' _ hsec hsec'' a hs o).trans ?_
  rw [h.orEqv_apply, h'.orEqv_apply]
  refine (LineOrientation.conj_congr (A₂ := (h'.eT (ϕ.obj a) (h.smooth_obj hs)).trans
      (h.eT a hs)) (Γ₂ := (h'.eK (ϕ.obj a) (h.smooth_obj hs)).trans (h.eK a hs))
      (fun v => eT_comp h h' hs v) (fun κ => eK_comp h h' hs κ) _
      (conj_mem_trans _ _ _ _ m1 m2) o).trans ?_
  exact (LineOrientation.conj_trans
    (hC' := (orPt B' (ϕ.obj a) (h.smooth_obj hs)).isFredholm_of_mem_linSet hF'.2)
    (hC'' := (orPt B a hs).isFredholm_of_mem_linSet hF.2) _ _ _ _ m1 m2
    (conj_mem_trans _ _ _ _ m1 m2) o).symm

/-- **Functoriality on `O_f`**: `(Ψ ∘ Φ)_* = Ψ_* ∘ Φ_*`, `(a, o) ↦ (ψϕ(a), …)`. -/
theorem orSpaceMap_comp (p : OrSpace f hF.2) :
    (h'.comp h).orSpaceMap hF hF'' (pullback_comp_of h h' hF'' hpb hpb') hsec hsec'' p =
      h'.orSpaceMap hF' hF'' hpb' hsec' hsec'' (h.orSpaceMap hF hF' hpb hsec hsec' p) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  change ((h'.comp h).orEqv hF hF'' (pullback_comp_of h h' hF'' hpb hpb') hsec hsec'' _
      (X.PObj.smoothVal_mem p.1)).symm p.2 =
    (h'.orEqv hF' hF'' hpb' hsec' hsec'' _ (h.smooth_obj (X.PObj.smoothVal_mem p.1))).symm
      ((h.orEqv hF hF' hpb hsec hsec' _ (X.PObj.smoothVal_mem p.1)).symm p.2)
  refine (Equiv.symm_apply_eq _).2 ?_
  refine Eq.trans ?_ (orEqv_comp h h' hF hF' hF'' hpb hpb' hsec hsec' hsec'' _ _ _).symm
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Functoriality of `|f̄|_*` on `|O_f|`**: `|Ψ ∘ Φ|_* = |Ψ|_* ∘ |Φ|_*`. -/
theorem orbitOrMap_comp (c : Quot (E.OrRel hF hsec)) :
    (h'.comp h).orbitOrMap hF hF'' (pullback_comp_of h h' hF'' hpb hpb') hsec hsec'' c =
      h'.orbitOrMap hF' hF'' hpb' hsec' hsec'' (h.orbitOrMap hF hF' hpb hsec hsec' c) := by
  induction c using Quot.ind with
  | mk p => exact congrArg (Quot.mk _) (orSpaceMap_comp h h' hF hF' hF'' hpb hpb' hsec hsec'
      hsec'' p)

end Or

/-- **Functoriality on `|X_∞|`**: `|ψ ∘ ϕ| = |ψ| ∘ |ϕ|`. -/
theorem smoothOrbitMap_comp (c : Quot X.SmoothRel) :
    (h'.comp h).smoothOrbitMap c = h'.smoothOrbitMap (h.smoothOrbitMap c) := by
  induction c using Quot.ind with
  | mk p => rfl

end EpStrongBundle.IsStrongBundleEquivalence

end EquivComp

end Polyfold
