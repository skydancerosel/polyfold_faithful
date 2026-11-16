import Polyfold.Chapter9.OrientationBasic

/-!
# Images of submanifolds under sc-diffeomorphisms

The image of a submanifold under an sc-diffeomorphism: its tangent spaces, frames and orientations,
and the oriented tangent vectors pushed forward by the tangent map. The branched equivalences that
use them are in `Chapter11/BranchedEquivalenceTangent.lean`.
-/

set_option maxSynthPendingDepth 3
open Set Function Module Submodule
noncomputable section
namespace Polyfold
universe u v w
namespace MPolyfold
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-- The chain rule on open sets between three M-polyfolds (the version of
`tangentMapOn_tangentMapOn_eq` for different M-polyfolds). -/
theorem tangentMapOn_tangentMapOn_eq_of_eqOn {f : X → Y} {g : Y → Z} {h : X → Z} {U U' W : Set X}
    {V : Set Y} (hf : P.IsScSmoothOn Q f U) (hg : Q.IsScSmoothOn S g V)
    (hh : P.IsScSmoothOn S h U') (hW : IsOpen W) (hWU : W ⊆ U) (hWU' : W ⊆ U')
    (hfW : MapsTo f W V) (heq : EqOn (g ∘ f) h W) {α : P.TangentSpace}
    (hα : α ∈ P.tangentPreimage W) :
    tangentMapOn hg (tangentMapOn hf α) = tangentMapOn hh α := by
  have hfW' : P.IsScSmoothOn Q f W := hf.mono hW hWU
  have h1 := tangentMapOn_comp hg hfW' hfW hα
  have h2 : tangentMapOn hfW' α = tangentMapOn hf α := tangentMapOn_mono hf hW hWU hα
  have h3 : tangentMapOn (hg.comp hfW' hfW) α = tangentMapOn hh α :=
    tangentMapOn_congr _ _ hW subset_rfl hWU' heq hα
  rw [Function.comp_apply, h2] at h1
  rw [← h1, h3]

/-- One inclusion of `T_{f(a)}(f(A)) = Tf(T_aA)` for an sc-diffeomorphism between open subsets
of two M-polyfolds. -/
theorem image_submanifoldTangent_subset_of_isScDiffeoOn {f : X → Y} {g : Y → X} {U : Set X}
    {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') {A : Set X}
    (hfA : Q.IsSmoothSubmanifold (f '' A)) (hAU : A ⊆ U) {a : X} (ha : a ∈ A) :
    tangentMapOn hf.isScSmoothOn '' P.submanifoldTangent A a ⊆
      Q.submanifoldTangent (f '' A) (f a) := by
  rintro _ ⟨α, hα, rfl⟩
  obtain ⟨hαa, d, hy, hfix⟩ := hα
  set d' := hfA.data ⟨a, ha, rfl⟩
  have hfa' : f a ∈ d'.V := hfA.mem_data_V ⟨a, ha, rfl⟩
  have hs := d.isScPlusRetractionOn.isScSmoothOn
  have hsa : d.s a = a := d.apply_eq_self ⟨ha, hy⟩
  set W := (d.V ∩ U) ∩ d.s ⁻¹' (U ∩ f ⁻¹' d'.V)
  have hW : IsOpen W := (hs.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    (d.isOpen.inter hf.isScSmoothOn.isOpen)
    (hf.isScSmoothOn.continuousOn.isOpen_inter_preimage hf.isScSmoothOn.isOpen d'.isOpen)
  have haW : a ∈ W := ⟨⟨hy, hAU ha⟩, by
    change d.s a ∈ U ∩ f ⁻¹' d'.V; rw [hsa]; exact ⟨hAU ha, hfa'⟩⟩
  have hαW : α ∈ P.tangentPreimage W := by change _ ∈ W; rw [hαa]; exact haW
  have hfs : P.IsScSmoothOn Q (f ∘ d.s) W :=
    hf.isScSmoothOn.comp (hs.mono hW fun _ hw => hw.1.1) fun w hw => hw.2.1
  have h1 : tangentMapOn hf.isScSmoothOn (d.tmap α) = tangentMapOn hfs α :=
    tangentMapOn_tangentMapOn_eq_of_eqOn hs hf.isScSmoothOn hfs hW (fun _ hw => hw.1.1) subset_rfl
      (fun w hw => hw.2.1) (fun _ _ => rfl) hαW
  rw [hfix] at h1
  have heq : EqOn (d'.s ∘ (f ∘ d.s)) (f ∘ d.s) W := fun w hw => by
    have h2 : d.s w ∈ d.s '' d.V := ⟨w, hw.1.1, rfl⟩
    rw [d.image] at h2
    exact d'.apply_eq_self ⟨⟨d.s w, h2.1, rfl⟩, hw.2.2⟩
  have h3 := tangentMapOn_tangentMapOn_eq_of_eqOn hfs d'.isScPlusRetractionOn.isScSmoothOn hfs hW
    subset_rfl subset_rfl (fun w hw => hw.2.2) heq hαW
  have hbase : Q.levelVal 1 (Q.tangentProj (tangentMapOn hf.isScSmoothOn α)) = f a := by
    rw [levelVal_tangentProj_tangentMapOn _ (show α ∈ P.tangentPreimage U from by
      change _ ∈ U; rw [hαa]; exact hAU ha), hαa]
  refine ⟨hbase, d', hfa', ?_⟩
  change tangentMapOn _ (tangentMapOn hf.isScSmoothOn α) = tangentMapOn hf.isScSmoothOn α
  rw [h1, h3]

/-- **`T_{f(a)}(f(A)) = Tf(T_aA)`** for an sc-diffeomorphism `f : U → U'` between open subsets of
two M-polyfolds and a smooth submanifold `A ⊆ U` (`submanifoldTangent_image` for `X = Y`). -/
theorem submanifoldTangent_image_of_isScDiffeoOn {f : X → Y} {g : Y → X} {U : Set X}
    {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (hAU : A ⊆ U) {a : X} (ha : a ∈ A) :
    Q.submanifoldTangent (f '' A) (f a) =
      tangentMapOn hf.isScSmoothOn '' P.submanifoldTangent A a := by
  have hfA := hA.image_of_isScDiffeoOn hf hAU
  refine Subset.antisymm (fun β hβ => ?_)
    (image_submanifoldTangent_subset_of_isScDiffeoOn hf hfA hAU ha)
  have hfAU' : f '' A ⊆ U' := image_subset_iff.2 fun y hy => hf.mapsTo (hAU hy)
  have hgf : g '' (f '' A) = A := by
    rw [image_image]
    exact (image_congr fun y hy => hf.left_inv y (hAU hy)).trans (image_id' A)
  have hga : g (f a) = a := hf.left_inv a (hAU ha)
  have h := image_submanifoldTangent_subset_of_isScDiffeoOn hf.symm (hgf.symm ▸ hA) hfAU'
    ⟨a, ha, rfl⟩
  rw [hgf, hga] at h
  have hβU' : β ∈ Q.tangentPreimage U' := by
    change _ ∈ U'; rw [hβ.1]; exact hf.mapsTo (hAU ha)
  exact ⟨_, h ⟨β, hβ, rfl⟩, hf.tangent.right_inv β hβU'⟩

/-- `chartVec_tangentMapOn` for an sc-diffeomorphism between open subsets of two M-polyfolds: the
chart vector of `Tf(α)` in `ψ` is that of `α` in the transported chart `ψ ∘ f`. -/
theorem chartVec_tangentMapOn_of_isScDiffeoOn {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y}
    (hf : P.IsScDiffeoOn Q f g U U') {ψ : MChart Y} (hψ : Q.IsChart ψ) {α : P.TangentSpace}
    (hα : P.levelVal 1 (P.tangentProj α) ∈ U ∩ f ⁻¹' ψ.source) :
    chartVec hψ (tangentMapOn hf.isScSmoothOn α) = chartVec (transportChart_isChart hf hψ) α := by
  set χ := transportChart hf ψ with hχdef
  have hχ : P.IsChart χ := transportChart_isChart hf hψ
  have hdom : TangentPre.fdomOn U χ f ψ = χ.source := by
    ext x
    simp only [TangentPre.fdomOn, hχdef, transportChart_source, mem_inter_iff, mem_preimage]
    tauto
  have hαW : α ∈ P.tangentPreimage (TangentPre.fdomOn U χ f ψ) := by
    rw [hdom]; exact hα
  have h1 := tangentChartMap_tangentMapOn hf.isScSmoothOn hχ hψ hαW
  have hαχ : α ∈ tangentChartSet χ := hα
  have hO : IsScRetract χ.model.E χ.model.C (χ '' TangentPre.fdomOn U χ f ψ) :=
    χ.isScRetract_image (TangentPre.fdomOn_subset U χ f ψ)
      (TangentPre.isOpen_fdomOn hf.isScSmoothOn χ ψ)
  have heq : EqOn (ψ ∘ f ∘ χ.symm) id (χ '' TangentPre.fdomOn U χ f ψ) := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, id]
    rw [χ.symm_apply_apply (TangentPre.fdomOn_subset U χ f ψ hx)]
    rfl
  have hmem : tangentChartMap hχ α ∈ retractTangent χ.model.E χ.model.C
      (χ '' TangentPre.fdomOn U χ f ψ) := by
    refine (TangentPre.mem_retractTangent_image_iff (TangentPre.fdomOn_subset U χ f ψ)
      (TangentPre.isOpen_fdomOn hf.isScSmoothOn χ ψ) ?_).2 (tangentChartMap_mem hχ hαχ)
    rw [tangentChartMap_fst hχ hαχ, P.toBase_levelLift hχ hαχ (levelVal_mem _)]
    exact ⟨_, hαW, rfl⟩
  unfold chartVec
  rw [h1]
  exact congrArg Prod.snd (retractTangentMap_id hO heq hmem)

/-- The image `(f(L), f_*(o))` of an oriented tangent set of `X` under a map `TX → TY` (for
`X = Y` this is `OrTangent.push`). -/
def OrTangent.map (f : P.TangentSpace → Q.TangentSpace) (g : OrTangent P) : OrTangent Q :=
  ⟨g.dim, f '' g.carrier, (fun v => f ∘ v) '' g.frames⟩

@[simp] theorem OrTangent.map_carrier (f : P.TangentSpace → Q.TangentSpace) (g : OrTangent P) :
    (g.map f).carrier = f '' g.carrier := rfl

theorem OrTangent.map_eq_push (f : P.TangentSpace → P.TangentSpace) (g : OrTangent P) :
    g.map f = g.push f := rfl

/-- **Oriented tangent sets are carried by sc-diffeomorphisms between different M-polyfolds**
(`IsOrientedAt.push_tangentMapOn` for `X = Y`). -/
theorem IsOrientedAt.map_tangentMapOn {f : X → Y} {f' : Y → X} {U : Set X} {U' : Set Y}
    (hf : P.IsScDiffeoOn Q f f' U U') {y : X} (hyU : y ∈ U) {g : OrTangent P}
    (h : P.IsOrientedAt y g) :
    Q.IsOrientedAt (f y) (g.map (tangentMapOn hf.isScSmoothOn)) := by
  have hL := h.1
  obtain ⟨ψ, hψ, hyψ⟩ := Q.exists_isChart_mem_source (f y)
  have hχ := transportChart_isChart hf hψ
  have hyχ : y ∈ (transportChart hf ψ).source := ⟨hyU, hyψ⟩
  obtain ⟨N, hN, hfin, hrank, ω, hO⟩ := h.isChartOrientation hχ hyχ
  have hcv : ∀ α ∈ g.carrier, chartVec hψ (tangentMapOn hf.isScSmoothOn α) = chartVec hχ α :=
    fun α hα => chartVec_tangentMapOn_of_isScDiffeoOn hf hψ (by rw [hL α hα]; exact hyχ)
  refine ⟨?_, ψ, hψ, hyψ, N, ?_, hfin, hrank, ω, ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    rw [levelVal_tangentProj_tangentMapOn hf.isScSmoothOn
      (show α ∈ P.tangentPreimage U from by change _ ∈ U; rw [hL α hα]; exact hyU), hL α hα]
  · refine hN.trans ?_
    rw [OrTangent.map_carrier, image_image]
    exact image_congr fun α hα => (hcv α hα).symm
  · change (fun v => tangentMapOn hf.isScSmoothOn ∘ v) '' g.frames =
      chartFrames hψ (tangentMapOn hf.isScSmoothOn '' g.carrier) N ω
    rw [hO]
    ext w
    constructor
    · rintro ⟨v, ⟨hv, b, hb, hbo⟩, rfl⟩
      exact ⟨fun i => mem_image_of_mem _ (hv i), b, fun i => (hb i).trans (hcv _ (hv i)).symm,
        hbo⟩
    · rintro ⟨hw, b, hb, hbo⟩
      choose u hu hfu using hw
      refine ⟨u, ⟨hu, b, fun i => (hb i).trans ?_, hbo⟩, funext hfu⟩
      rw [← hfu i]
      exact hcv _ (hu i)

/-- The vectors of the frames of `T_y(M, o)` lie over `y`. -/
theorem SubmanifoldOrientation.levelVal_frames {M : Set X} {n : ℕ}
    (o : P.SubmanifoldOrientation M n) {y : X} (hy : y ∈ M) {v : Fin n → P.TangentSpace}
    (hv : v ∈ o.frames y) (i : Fin n) : P.levelVal 1 (P.tangentProj (v i)) = y :=
  ((o.isOrientedAt y hy).mem_carrier hv i).1

/-- **An orientation of a submanifold moved by an sc-diffeomorphism** `f : U → U'` between open
subsets of two M-polyfolds: the frames of `T_{f(y)} f(M)` are the images `Tf ∘ v` of the frames
of `T_yM`; continuity is read in the chart `φ ∘ f⁻¹` (`transportChart` of the inverse). -/
def SubmanifoldOrientation.mapDiffeo {M : Set X} {n : ℕ} (o : P.SubmanifoldOrientation M n)
    (hM : P.IsSmoothSubmanifold M) {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y}
    (hf : P.IsScDiffeoOn Q f g U U') (hMU : M ⊆ U) :
    Q.SubmanifoldOrientation (f '' M) n where
  frames z := (fun v => tangentMapOn hf.isScSmoothOn ∘ v) '' o.frames (g z)
  isOrientedAt := by
    rintro _ ⟨y, hy, rfl⟩
    have h := (o.isOrientedAt y hy).map_tangentMapOn hf (hMU hy)
    rw [submanifoldTangent_image_of_isScDiffeoOn hf hM hMU hy, hf.left_inv y (hMU hy)]
    exact h
  continuous hn := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨φ, hφ, V, hV, hyV, hVφ, e, he, hc⟩ := o.continuous hn y hy
    have hφ' := transportChart_isChart hf.symm hφ
    have hgy : g (f y) = y := hf.left_inv y (hMU hy)
    refine ⟨transportChart hf.symm φ, hφ', U' ∩ g ⁻¹' V,
      hf.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hf.isScSmoothOn_inv.isOpen hV,
      ⟨hf.mapsTo (hMU hy), by rw [mem_preimage, hgy]; exact hyV⟩,
      fun w hw => ⟨hw.1, hVφ hw.2⟩,
      fun w i => tangentMapOn hf.isScSmoothOn (e (g w) i), ?_, ?_⟩
    · rintro _ ⟨⟨u, hu, rfl⟩, -, hV'⟩
      have hgu := hf.left_inv u (hMU hu)
      rw [mem_preimage, hgu] at hV'
      simp only [hgu]
      exact ⟨e u, he u ⟨hu, hV'⟩, rfl⟩
    · have hmaps : MapsTo g (f '' M ∩ (U' ∩ g ⁻¹' V)) (M ∩ V) := by
        rintro _ ⟨⟨u, hu, rfl⟩, -, hV'⟩
        have hgu := hf.left_inv u (hMU hu)
        rw [mem_preimage, hgu] at hV'
        rw [hgu]
        exact ⟨hu, hV'⟩
      have hcg : ContinuousOn (fun w i => chartVec hφ (e (g w) i)) (f '' M ∩ (U' ∩ g ⁻¹' V)) :=
        hc.comp (hf.isScSmoothOn_inv.continuousOn.mono fun w hw => hw.2.1) hmaps
      refine hcg.congr fun w hw => ?_
      obtain ⟨⟨u, hu, rfl⟩, -, hV'⟩ := hw
      have hgu : g (f u) = u := hf.left_inv u (hMU hu)
      rw [mem_preimage, hgu] at hV'
      funext i
      have hbase : P.levelVal 1 (P.tangentProj (e u i)) = u :=
        o.levelVal_frames hu (he u ⟨hu, hV'⟩) i
      have hαU : e u i ∈ P.tangentPreimage U := by
        change _ ∈ U; rw [hbase]; exact hMU hu
      have h1 := chartVec_tangentMapOn_of_isScDiffeoOn hf.symm hφ
        (α := tangentMapOn hf.isScSmoothOn (e u i)) (by
          rw [levelVal_tangentProj_tangentMapOn hf.isScSmoothOn hαU, hbase]
          exact ⟨hf.mapsTo (hMU hu), by rw [mem_preimage, hgu]; exact hVφ hV'⟩)
      simp only [hgu]
      rw [← h1]
      exact congrArg _ (hf.tangent.left_inv _ hαU)

@[simp] theorem SubmanifoldOrientation.mapDiffeo_frames {M : Set X} {n : ℕ}
    (o : P.SubmanifoldOrientation M n) (hM : P.IsSmoothSubmanifold M) {f : X → Y} {g : Y → X}
    {U : Set X} {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') (hMU : M ⊆ U) (z : Y) :
    (o.mapDiffeo hM hf hMU).frames z =
      (fun v => tangentMapOn hf.isScSmoothOn ∘ v) '' o.frames (g z) := rfl

/-- `T_{f(y)}(f(M), f_*o) = Tf(T_y(M, o))`. -/
theorem SubmanifoldOrientation.mapDiffeo_tangent {M : Set X} {n : ℕ}
    (o : P.SubmanifoldOrientation M n) (hM : P.IsSmoothSubmanifold M) {f : X → Y} {g : Y → X}
    {U : Set X} {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') (hMU : M ⊆ U) {y : X}
    (hy : y ∈ M) :
    (o.mapDiffeo hM hf hMU).tangent (f y) = (o.tangent y).map (tangentMapOn hf.isScSmoothOn) := by
  simp only [SubmanifoldOrientation.tangent, OrTangent.map, mapDiffeo_frames,
    hf.left_inv y (hMU hy), submanifoldTangent_image_of_isScDiffeoOn hf hM hMU hy]

/-- The image of an open subset of `U` under an sc-diffeomorphism `f : U → U'` is open. -/
theorem IsScDiffeoOn.isOpen_image_of_subset {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y}
    (hf : P.IsScDiffeoOn Q f g U U') {A : Set X} (hA : IsOpen A) (hAU : A ⊆ U) :
    IsOpen (f '' A) := by
  have h : f '' A = U' ∩ g ⁻¹' A := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hf.mapsTo (hAU hx), by rw [mem_preimage, hf.left_inv x (hAU hx)]; exact hx⟩
    · rintro ⟨hy, hgy⟩
      exact ⟨g y, hgy, hf.right_inv y hy⟩
  rw [h]
  exact hf.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hf.isScSmoothOn_inv.isOpen hA

end MPolyfold
end Polyfold
end
