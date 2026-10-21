import FCAppendix.Affine.Uniform07Finishing.Native.SourceSuccessBadEvents
import FCAppendix.Affine.Uniform07Finishing.Native.UpperFloorReplacement

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open StrictNative ConditionalSuccess

variable {m : ℕ} [Nonempty (Fin m)]

omit [Nonempty (Fin m)] in
theorem source_deviation_context_floor_aligned {R R' : ℝ}
    (d d' : UserProfile m 2) (hd : ∀ k, FloorAlignedDraw R R' (d k) (d' k))
    (i : Fin m) (a : JointAction 2) (ha : a.bid< R) (ha' : a.bid< R')
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    observedContext R j (deviationList i a d τ j)=
      observedContext R' j (deviationList i a d' τ j) := by
  let d₀:=Function.update d i ((0,a),τ)
  let d₁:=Function.update d' i ((0,a),τ)
  have hdu : ∀ k, FloorAlignedDraw R R' (d₀ k) (d₁ k) := by
    intro k
    by_cases hk:k=i
    · subst k
      simp only [d₀,d₁,Function.update_self]
      exact ⟨rfl,rfl,Or.inl ⟨rfl,ha,ha'⟩⟩
    · simpa only [d₀,d₁,Function.update_of_ne hk] using hd k
  have h₀:observe (drawsRealization d₀) j=deviationList i a d τ j :=
    observe_insertDraw i (((0,a),τ),(d,fun _ : Fin 2=>(0:unitInterval))) j
  have h₁:observe (drawsRealization d₁) j=deviationList i a d' τ j :=
    observe_insertDraw i (((0,a),τ),(d',fun _ : Fin 2=>(0:unitInterval))) j
  have h:=observedContext_floor_aligned d₀ d₁ hdu j
  rwa [h₀,h₁] at h

omit [Nonempty (Fin m)] in
theorem source_deviation_focal_contact_eq (d d' : UserProfile m 2)
    (i : Fin m) (a : JointAction 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    deviationList i a d τ j i=deviationList i a d' τ j i := by
  simp only [deviationList,observe,deviate,Function.update_self]

section Floors
variable (row : Uniform07.Row) (hm : 2≤ m) (hc : 1≤ Uniform07.capacity m)
  {R R' Λ z width ε : ℝ}
  (hR : 0< R) (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
  (hR' : 0< R') (hUR' : Early.bidCap row< R') (hR't : R'< Uniform07.cutoff row)
  (hΛ : (54/100:ℝ)*Uniform07.cutoff row<Λ)
  (PL : ProbabilityMeasure (ℝ×JointAction 2))
  (hLvalue : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=
    (sourceLowerValueLaw row : Measure ℝ))
  (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)),
    x.2.bid≤ Early.bidCap row ∧ x.2.routeCount=2)

local notation "α" => literalSourceAlpha row Λ z width ε
local notation "hα" => measurable_literalSourceAlpha row hΛ z width ε
local notation "Γ" => sourceNativeGame row hc R Λ
  (source_guard_multiplier_positive row hΛ) PL α hα
local notation "Γ'" => sourceNativeGame row hc R' Λ
  (source_guard_multiplier_positive row hΛ) PL α hα

include hm hR hUR hRt hR' hUR' hR't in
theorem sourceSuccessPlan_floor_invariant :
    sourceSuccessPlan row hc R Λ z width ε PL=
      sourceSuccessPlan row hc R' Λ z width ε PL := by
  unfold sourceSuccessPlan
  rw [sourceSeedMeasure_floor_invariant row hm hc hR hUR hRt hR' hUR' hR't PL]

include hm hR hUR hRt hR' hUR' hR't in
theorem sourceSuccessGood_floor_aligned
    (d d' : UserProfile m 2) (hd : ∀ k, FloorAlignedDraw R R' (d k) (d' k))
    (i : Fin m) (a : JointAction 2) (ha : a.bid< R) (ha' : a.bid< R') :
    d∈sourceSuccessGood row hc R Λ z width ε PL i a ↔
      d'∈sourceSuccessGood row hc R' Λ z width ε PL i a := by
  unfold sourceSuccessGood
  simp only [mem_setOf_eq]
  apply forall_congr'
  intro τ
  apply forall_congr'
  intro j
  rw [source_deviation_focal_contact_eq d d' i a τ j,
    sourceSuccessPlan_floor_invariant row hm hc hR hUR hRt hR' hUR' hR't PL,
    source_deviation_context_floor_aligned d d' hd i a ha ha' τ j]

include hm hR hUR hRt hR' hUR' hR't hLvalue hLroute in

theorem sourceSuccessGood_bad_mass_floor_invariant
    (i : Fin m) (a : JointAction 2) (ha : a.bid< R) (ha' : a.bid< R') :
    (userProfileLaw Γ').real (sourceSuccessGood row hc R' Λ z width ε PL i a)ᶜ=
      (userProfileLaw Γ).real (sourceSuccessGood row hc R Λ z width ε PL i a)ᶜ := by
  let f:=fun d : UserProfile m 2=>replaceSourceUpperDraw row m hc R' ∘ d
  have hp:=sourceNativeGame_replace_profile_measurePreserving row hm hc hR hUR hRt
    hR' hR't (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute α hα
  have hg:=sourceNativeGame_replace_aligned row hm hc hR hUR hRt hR' hUR' hR't
    (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute α hα
  have he : f ⁻¹' (sourceSuccessGood row hc R' Λ z width ε PL i a)ᶜ =ᵐ[userProfileLaw Γ]
      (sourceSuccessGood row hc R Λ z width ε PL i a)ᶜ := by
    filter_upwards [hg] with d hd
    apply propext
    exact not_congr (sourceSuccessGood_floor_aligned row hm hc hR hUR hRt hR' hUR' hR't PL
      d (f d) hd i a ha ha').symm
  change ENNReal.toReal ((userProfileLaw Γ') (sourceSuccessGood row hc R' Λ z width ε PL i a)ᶜ)=_
  rw [←hp.map_eq,Measure.map_apply hp.measurable
    (measurableSet_sourceSuccessGood row hc R' Λ z width ε hΛ PL i a).compl,
    measure_congr he]
  rfl

end Floors
end FCAppendix.Affine.Uniform07Finishing
