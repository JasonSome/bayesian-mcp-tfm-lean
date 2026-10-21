import FCAppendix.Affine.Tail04.TwoFocalGuard

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators

section Definitions
variable {X Ω : Type*} (N : ℕ) (row : Ω→ Fin N→ X×unitInterval) (target : Ω→ Fin (N+1))
    (active private0 private1 : X→ Bool) (p : X→ unitInterval)

def flaggedMixedBit (focal : Bool) (x : Ω) (i : Fin (N+1)) : Bool :=
  if i=target x then false else Fin.cases focal (fun j : Fin N => activeFlag active p (row x j)) i

def flaggedMixedCount (focal : Bool) (x : Ω) : ℕ :=
  boolCount (flaggedMixedBit N row target active p focal x)

def flaggedReciprocal (bid : X→ℝ) (b : ℝ) (focal : Bool) : Ω→ℝ :=
  forcedMean N (Empirical.markedStatistic p (reciprocalWeight active bid))
    (if focal then 1/b else 0) row target

def flaggedGuardWeight (bid : X→ℝ) (ξ share ρ B R Rp width b : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg focal : Bool) (x : Ω) : ℝ :=
  scalarSourceWeight N (activeCount N row active x) (flaggedMixedCount N row target active p focal x)
    (privateCount N row private0 x) (privateCount N row private1 x)
    ξ share ρ B R Rp width hshare reg (flaggedReciprocal N row target active p bid b focal x)

def flaggedGuardError (bid : X→ℝ) (b abar mbar hbar wbar : ℝ) (focal : Bool) (x : Ω) : ℝ :=
  guardError N (activeCount N row active x) (flaggedMixedCount N row target active p focal x)
    (privateCount N row private0 x) (privateCount N row private1 x)
    (flaggedReciprocal N row target active p bid b focal x) abar mbar hbar wbar

theorem flaggedMixedCount_le_active (focal : Bool) (x : Ω) :
    flaggedMixedCount N row target active p focal x≤ activeCount N row active x := by
  unfold flaggedMixedCount activeCount boolCount
  apply Finset.sum_le_sum
  intro i _
  have hle (j : Fin (N+1)) :
      (if (Fin.cases focal (fun k : Fin N => activeFlag active p (row x k)) j : Bool)
        then (1:ℕ) else 0) ≤
      if (Fin.cases true (fun k : Fin N => active (row x k).1) j : Bool) then 1 else 0 := by
    refine Fin.cases ?_ (fun k => ?_) j
    · cases focal <;> norm_num
    · cases ha : active (row x k).1 <;> cases hf : Empirical.flag (p (row x k).1) (row x k).2 <;>
        simp [activeFlag,ha,hf]
  unfold flaggedMixedBit
  by_cases hi : i = target x
  · simp only [if_pos hi, Bool.false_eq_true, ↓reduceIte]
    exact Nat.zero_le _
  · simpa only [if_neg hi] using hle i

theorem flaggedMixedCount_normalized (focal : Bool) (x : Ω) :
    (flaggedMixedCount N row target active p focal x:ℝ)/N=
      forcedMean N (Empirical.markedStatistic p (indicator active))
        (if focal then 1 else 0) row target x := by
  rw [flaggedMixedCount,boolCount_real]
  unfold forcedMean
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i=target x
  · simp [flaggedMixedBit,hi]
  · simp only [flaggedMixedBit,if_neg hi]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [prefixWeight]
    · exact activeFlag_weight active p (row x j)

theorem flaggedMixedCount_true (x : Ω) :
    flaggedMixedCount N row target active p true x=mixedCount N row target active p x := rfl

theorem flaggedGuardWeight_true (bid : X→ℝ) (ξ share ρ B R Rp width b : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg : Bool) :
    flaggedGuardWeight N row target active private0 private1 p bid ξ share ρ B R Rp width b hshare reg true=
      originalGuardWeight N row target active private0 private1 p bid ξ share ρ B R Rp width b hshare reg := rfl

end Definitions

section Original
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
variable (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (N : ℕ) (hN : 0< N) (row : Ω→ Fin N→ X×unitInterval)
variable (hrow : MeasurePreserving row ν
  (Measure.pi (fun _ : Fin N => μ.prod (volume : Measure unitInterval))))
variable (target : Ω→ Fin (N+1)) (htarget : Measurable target)
variable (active private0 private1 : X→ Bool)
variable (hactive : Measurable active) (hprivate0 : Measurable private0) (hprivate1 : Measurable private1)
variable (p : X→ unitInterval) (hp : Measurable p) (bid : X→ℝ) (hbid : Measurable bid)

include hrow htarget hactive hp in
omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem measurable_flaggedMixedCount (focal : Bool) :
    Measurable (flaggedMixedCount N row target active p focal) := by
  apply measurable_boolCount
  intro i
  apply Measurable.ite (measurableSet_eq_fun measurable_const htarget) measurable_const
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_const
  · exact (measurable_activeFlag active hactive p hp).comp ((measurable_pi_apply j).comp hrow.measurable)

include μ ν hrow htarget hactive hp hbid in
omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem measurable_flaggedReciprocal (b : ℝ) (focal : Bool) :
    Measurable (flaggedReciprocal N row target active p bid b focal) :=
  measurable_forcedMean (μ.prod (volume : Measure unitInterval)) ν N row hrow
    (Empirical.markedStatistic p (reciprocalWeight active bid))
    (Empirical.measurable_markedStatistic p hp (reciprocalWeight active bid)
      (measurable_reciprocalWeight active hactive bid hbid))
    (if focal then 1/b else 0) target htarget

include μ hN hrow htarget hactive hp hbid in
omit [IsProbabilityMeasure μ] in
theorem integrable_flaggedReciprocal (b : ℝ) (hb : 1≤ b) (focal : Bool) :
    Integrable (flaggedReciprocal N row target active p bid b focal) ν :=
  integrable_forcedMean (μ.prod (volume : Measure unitInterval)) ν N hN row hrow
    (Empirical.markedStatistic p (reciprocalWeight active bid))
    (Empirical.measurable_markedStatistic p hp (reciprocalWeight active bid)
      (measurable_reciprocalWeight active hactive bid hbid))
    (Empirical.markedStatistic_bounds p (reciprocalWeight active bid) (reciprocalWeight_bounds active bid))
    (if focal then 1/b else 0) (focalReciprocal_bounds hb focal) target htarget

include hN hrow htarget hactive hp in
theorem actual_flagged_mixed_L1 (focal : Bool) :
    (∫ x,|(flaggedMixedCount N row target active p focal x:ℝ)/N-
      ∫ y,(p y:ℝ)*indicator active y ∂μ| ∂ν)≤1/Real.sqrt N+1/(N:ℝ) := by
  simp_rw [flaggedMixedCount_normalized]
  exact original_marked_forced_L1 μ ν N hN row hrow p hp (indicator active)
    (measurable_indicator active hactive) (indicator_bounds active) (if focal then 1 else 0)
    (by cases focal <;> norm_num) target htarget

include hN hrow htarget hactive hp hbid in
theorem actual_flagged_reciprocal_L1 (b : ℝ) (hb : 1≤ b) (focal : Bool) :
    (∫ x,|flaggedReciprocal N row target active p bid b focal x-
      ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ| ∂ν)≤1/Real.sqrt N+1/(N:ℝ) :=
  original_marked_forced_L1 μ ν N hN row hrow p hp (reciprocalWeight active bid)
    (measurable_reciprocalWeight active hactive bid hbid) (reciprocalWeight_bounds active bid)
    (if focal then 1/b else 0) (focalReciprocal_bounds hb focal) target htarget

omit [MeasurableSpace X] [MeasurableSpace Ω] in
theorem flagged_count_bounds (focal : Bool) (x : Ω) :
    activeCount N row active x≤ N+1 ∧ flaggedMixedCount N row target active p focal x≤ N+1 ∧
      privateCount N row private0 x≤ N+1 ∧ privateCount N row private1 x≤ N+1 := by
  have h := source_count_bounds N row target active private0 private1 p x
  exact ⟨h.1,(flaggedMixedCount_le_active N row target active p focal x).trans h.1,h.2.2⟩

omit [IsProbabilityMeasure μ] in
include μ hN hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem integrable_flaggedGuardError (b abar mbar hbar wbar : ℝ) (hb : 1≤ b) (focal : Bool) :
    Integrable (flaggedGuardError N row target active private0 private1 p bid b abar mbar hbar wbar focal) ν := by
  apply integrable_guardError ν N (N+1) _ _ _ _
    (measurable_activeCount N row active hrow.measurable hactive)
    (measurable_flaggedMixedCount μ ν N row hrow target htarget active hactive p hp focal)
    (measurable_privateCount N row private0 hrow.measurable hprivate0)
    (measurable_privateCount N row private1 hrow.measurable hprivate1)
    (fun x => (flagged_count_bounds N row target active private0 private1 p focal x).1)
    (fun x => (flagged_count_bounds N row target active private0 private1 p focal x).2.1)
    (fun x => (flagged_count_bounds N row target active private0 private1 p focal x).2.2.1)
    (fun x => (flagged_count_bounds N row target active private0 private1 p focal x).2.2.2)
    (flaggedReciprocal N row target active p bid b focal)
    (integrable_flaggedReciprocal μ ν N hN row hrow target htarget active hactive p hp bid hbid b hb focal)

include hN hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem original_flagged_guardError_L1 (b : ℝ) (hb : 1≤ b) (focal : Bool)
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ)) :
    let abar := ∫ x,indicator active x ∂μ
    let mbar := ∫ x,(p x:ℝ)*indicator active x ∂μ
    let hbar := ∫ x,indicator private0 x ∂μ
    let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
    (∫ x,flaggedGuardError N row target active private0 private1 p bid b abar mbar hbar wbar focal x ∂ν)≤
      5/Real.sqrt N+4/(N:ℝ) := by
  dsimp only
  apply integrated_guardError ν N (N+1) _ _ _ _
    (measurable_activeCount N row active hrow.measurable hactive)
    (measurable_flaggedMixedCount μ ν N row hrow target htarget active hactive p hp focal)
    (measurable_privateCount N row private0 hrow.measurable hprivate0)
    (measurable_privateCount N row private1 hrow.measurable hprivate1)
    (fun x => (flagged_count_bounds N row target active private0 private1 p focal x).1)
    (fun x => (flagged_count_bounds N row target active private0 private1 p focal x).2.1)
    (fun x => (flagged_count_bounds N row target active private0 private1 p focal x).2.2.1)
    (fun x => (flagged_count_bounds N row target active private0 private1 p focal x).2.2.2)
    (flaggedReciprocal N row target active p bid b focal)
    (integrable_flaggedReciprocal μ ν N hN row hrow target htarget active hactive p hp bid hbid b hb focal)
  · exact actual_active_count_L1 μ ν N hN row hrow active hactive
  · exact actual_flagged_mixed_L1 μ ν N hN row hrow target htarget active hactive p hp focal
  · exact actual_private_count_L1 μ ν N hN row hrow private0 hprivate0
  · simpa only [←hfair] using actual_private_count_L1 μ ν N hN row hrow private1 hprivate1
  · exact actual_flagged_reciprocal_L1 μ ν N hN row hrow target htarget active hactive p hp bid hbid b hb focal

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
include μ ν hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem measurable_flaggedGuardWeight (ξ share ρ B R Rp width b : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg focal : Bool) :
    Measurable (flaggedGuardWeight N row target active private0 private1 p bid
      ξ share ρ B R Rp width b hshare reg focal) :=
  measurable_scalarSourceWeight N _ _ _ _
    (measurable_activeCount N row active hrow.measurable hactive)
    (measurable_flaggedMixedCount μ ν N row hrow target htarget active hactive p hp focal)
    (measurable_privateCount N row private0 hrow.measurable hprivate0)
    (measurable_privateCount N row private1 hrow.measurable hprivate1)
    ξ share ρ B R Rp width hshare reg _
    (measurable_flaggedReciprocal μ ν N row hrow target htarget active hactive p hp bid hbid b focal)

omit [IsProbabilityMeasure μ] in
include μ hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem integrable_flaggedGuardWeight (ξ share ρ B R Rp width b : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg focal : Bool) :
    Integrable (flaggedGuardWeight N row target active private0 private1 p bid
      ξ share ρ B R Rp width b hshare reg focal) ν := by
  apply Integrable.of_bound
    (measurable_flaggedGuardWeight μ ν N row hrow target htarget active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ B R Rp width b hshare reg focal).aestronglyMeasurable 1
  exact ae_of_all _ (fun x => by
    have hb := scalarSourceWeight_bounds N (activeCount N row active x)
      (flaggedMixedCount N row target active p focal x) (privateCount N row private0 x) (privateCount N row private1 x)
      ξ share ρ B R Rp width hshare reg (flaggedReciprocal N row target active p bid b focal x)
    change flaggedGuardWeight N row target active private0 private1 p bid
      ξ share ρ B R Rp width b hshare reg focal x∈Icc (0:ℝ) 1 at hb
    rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
    exact hb.2)

include hN hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem original_flagged_guard_defect_L1 (ξ share ρ B R Rp width γ δ b : ℝ) (reg focal : Bool)
    (hξ : ξ∈Icc (0:ℝ) 1) (hshare : share∈Icc (0:ℝ) 1)
    (hshareLo : lowerShare reg≤ share) (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤ B)
    (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1) (hδ : 0< δ) (hb : 1≤ b)
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ)) :
    let abar := ∫ x,indicator active x ∂μ
    let mbar := ∫ x,(p x:ℝ)*indicator active x ∂μ
    let hbar := ∫ x,indicator private0 x ∂μ
    let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
    δ≤ mbar/2 → δ≤ wbar/2 → 4*δ≤ ρ-(abar-mbar)/2-hbar → 10*δ≤ γ*wbar →
    (1-ξ)*B+2*γ≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg)/wbar →
    populationNumerator ξ ρ abar mbar hbar 1/wbar+2*γ≤1 →
    (if reg then Rp+2*γ≤ populationNumerator ξ ρ abar mbar hbar share/wbar
      else populationNumerator ξ ρ abar mbar hbar share/wbar+2*γ≤ R) →
    (∫ x,1-flaggedGuardWeight N row target active private0 private1 p bid
      ξ share ρ B R Rp width b hshare reg focal x ∂ν)≤(5/Real.sqrt N+4/(N:ℝ))/δ := by
  dsimp only
  intro hδm hδw hδc hδγ hlo hhi hmean
  let abar := ∫ x,indicator active x ∂μ
  let mbar := ∫ x,(p x:ℝ)*indicator active x ∂μ
  let hbar := ∫ x,indicator private0 x ∂μ
  let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
  let Z := flaggedGuardError N row target active private0 private1 p bid b abar mbar hbar wbar focal
  have hhbar : 0≤ hbar := integral_nonneg fun y => (indicator_bounds private0 y).1
  have hpnt (x : Ω) : 1-flaggedGuardWeight N row target active private0 private1 p bid
      ξ share ρ B R Rp width b hshare reg focal x≤ Z x/δ :=
    (scalarSourceWeight_defect_le N (activeCount N row active x)
      (flaggedMixedCount N row target active p focal x) (privateCount N row private0 x) (privateCount N row private1 x)
      hN (flaggedMixedCount_le_active N row target active p focal x)
      ξ share ρ B R Rp width γ δ (flaggedReciprocal N row target active p bid b focal x)
      abar mbar hbar wbar reg hξ hshare hshareLo hρ hB hhbar hw hwγ hγ1 hδ
      hδm hδw hδc hδγ hlo hhi hmean).2
  have hiZ := integrable_flaggedGuardError μ ν N hN row hrow target htarget active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid b abar mbar hbar wbar hb focal
  have hiw := integrable_flaggedGuardWeight μ ν N row hrow target htarget active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ B R Rp width b hshare reg focal
  calc
    _ ≤ ∫ x,Z x/δ ∂ν := integral_mono_ae ((integrable_const 1).sub hiw) (hiZ.div_const δ)
      (ae_of_all _ hpnt)
    _ = (∫ x,Z x ∂ν)/δ := by simp only [div_eq_mul_inv,integral_mul_const]
    _ ≤ _ := div_le_div_of_nonneg_right
      (original_flagged_guardError_L1 μ ν N hN row hrow target htarget active private0 private1
        hactive hprivate0 hprivate1 p hp bid hbid b hb focal hfair) hδ.le

end Original
end FCAppendix.Affine.Tail04.MenuError
