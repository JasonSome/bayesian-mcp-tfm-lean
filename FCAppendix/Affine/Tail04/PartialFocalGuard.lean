import FCAppendix.Affine.Tail04.OneFocalFlags

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal NativeTypicalCount
open scoped BigOperators

def partialOffset (side j : Fin 2) : ℕ := if side=j then 1 else 0

theorem partialOffset_le_one (side j : Fin 2) : partialOffset side j≤1 := by
  unfold partialOffset
  split_ifs <;> omega

theorem partialOffset_sum (side : Fin 2) :
    (partialOffset side 0:ℝ)+(partialOffset side 1:ℝ)=1 := by
  fin_cases side <;> norm_num [partialOffset]

section Definitions
variable {X Ω : Type*} (N : ℕ) (row : Ω→ Fin N→ X×unitInterval) (target : Ω→ Fin (N+1))
    (active private0 private1 : X→ Bool) (p : X→ unitInterval) (bid : X→ℝ)

def partialPrivateCount (privateClass : X→ Bool) (side j : Fin 2) (x : Ω) : ℕ :=
  privateCount N row privateClass x+partialOffset side j

def partialGuardError (abar mbar hbar wbar : ℝ) (side : Fin 2) (x : Ω) : ℝ :=
  guardError N (privateCount N row active x) (flaggedMixedCount N row target active p false x)
    (partialPrivateCount N row private0 side 0 x) (partialPrivateCount N row private1 side 1 x)
    (flaggedReciprocal N row target active p bid 1 false x) abar mbar hbar wbar

def partialGuardWeight (ξ share ρ B R Rp width : ℝ) (hshare : share∈Icc (0:ℝ) 1)
    (reg : Bool) (side : Fin 2) (x : Ω) : ℝ :=
  scalarSourceWeight N (privateCount N row active x) (flaggedMixedCount N row target active p false x)
    (partialPrivateCount N row private0 side 0 x) (partialPrivateCount N row private1 side 1 x)
    ξ share ρ B R Rp width hshare reg (flaggedReciprocal N row target active p bid 1 false x)

theorem partial_mixed_le_active (x : Ω) :
    flaggedMixedCount N row target active p false x≤ privateCount N row active x := by
  unfold flaggedMixedCount privateCount boolCount
  rw [Fin.sum_univ_succ]
  simp only [flaggedMixedBit,Fin.cases_zero,Fin.cases_succ,ite_self,
    Bool.false_eq_true,ite_false,zero_add]
  apply Finset.sum_le_sum
  intro i _
  by_cases ht : i.succ = target x
  · simp only [if_pos ht,Bool.false_eq_true,ite_false]
    exact Nat.zero_le _
  · simp only [if_neg ht]
    unfold activeFlag
    by_cases ha : active (row x i).1 = true
    · simp only [ha,ite_true]
      split_ifs <;> omega
    · simp [ha]

theorem partialPrivateCount_normalized (privateClass : X→ Bool) (side j : Fin 2) (x : Ω) :
    (partialPrivateCount N row privateClass side j x:ℝ)/N=
      insertedMean N (fun z : X×unitInterval => indicator privateClass z.1)
        (partialOffset side j) row x := by
  unfold partialPrivateCount
  rw [Nat.cast_add,add_div,privateCount_normalized]
  rfl

theorem partial_counts_bounded (side : Fin 2) (x : Ω) :
    privateCount N row active x≤ N+1 ∧ flaggedMixedCount N row target active p false x≤ N+1 ∧
      partialPrivateCount N row private0 side 0 x≤ N+1 ∧
      partialPrivateCount N row private1 side 1 x≤ N+1 := by
  have hc (privateClass : X→ Bool) : privateCount N row privateClass x≤ N := by
    simpa only [privateCount,Fintype.card_fin] using boolCount_le_card (fun i : Fin N => privateClass (row x i).1)
  exact ⟨(hc active).trans (by omega),
    (partial_mixed_le_active N row target active p x).trans ((hc active).trans (by omega)),
    Nat.add_le_add (hc private0) (partialOffset_le_one side 0),
    Nat.add_le_add (hc private1) (partialOffset_le_one side 1)⟩

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

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
include hrow in
theorem measurable_partialPrivateCount (privateClass : X→ Bool) (hprivate : Measurable privateClass)
    (side j : Fin 2) : Measurable (partialPrivateCount N row privateClass side j) :=
  (measurable_privateCount N row privateClass hrow.measurable hprivate).add measurable_const

include hN hrow in
theorem partial_private_L1 (privateClass : X→ Bool) (hprivate : Measurable privateClass) (side j : Fin 2) :
    (∫ x,|(partialPrivateCount N row privateClass side j x:ℝ)/N-∫ y,indicator privateClass y ∂μ| ∂ν)≤
      1/Real.sqrt N+(partialOffset side j:ℝ)/(N:ℝ) := by
  simp_rw [partialPrivateCount_normalized]
  simpa only [integral_indicator_fst μ privateClass hprivate] using
    original_inserted_exact_L1 (μ.prod (volume : Measure unitInterval)) ν N hN row hrow
      (fun z : X×unitInterval => indicator privateClass z.1)
      ((measurable_indicator privateClass hprivate).comp measurable_fst)
      (fun z => indicator_bounds privateClass z.1) (partialOffset side j) (Nat.cast_nonneg _)

omit [IsProbabilityMeasure μ] in
include μ hN hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem integrable_partialGuardError (abar mbar hbar wbar : ℝ) (side : Fin 2) :
    Integrable (partialGuardError N row target active private0 private1 p bid abar mbar hbar wbar side) ν := by
  apply integrable_guardError ν N (N+1) _ _ _ _
    (measurable_privateCount N row active hrow.measurable hactive)
    (measurable_flaggedMixedCount μ ν N row hrow target htarget active hactive p hp false)
    (measurable_partialPrivateCount μ ν N row hrow private0 hprivate0 side 0)
    (measurable_partialPrivateCount μ ν N row hrow private1 hprivate1 side 1)
    (fun x => (partial_counts_bounded N row target active private0 private1 p side x).1)
    (fun x => (partial_counts_bounded N row target active private0 private1 p side x).2.1)
    (fun x => (partial_counts_bounded N row target active private0 private1 p side x).2.2.1)
    (fun x => (partial_counts_bounded N row target active private0 private1 p side x).2.2.2)
    (flaggedReciprocal N row target active p bid 1 false)
    (integrable_flaggedReciprocal μ ν N hN row hrow target htarget active hactive p hp bid hbid 1 (by norm_num) false)

include hN hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem original_partial_guardError_L1 (side : Fin 2)
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ)) :
    let abar := ∫ x,indicator active x ∂μ
    let mbar := ∫ x,(p x:ℝ)*indicator active x ∂μ
    let hbar := ∫ x,indicator private0 x ∂μ
    let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
    (∫ x,partialGuardError N row target active private0 private1 p bid abar mbar hbar wbar side x ∂ν)≤
      5/Real.sqrt N+4/(N:ℝ) := by
  dsimp only
  have hA := actual_private_count_L1 μ ν N hN row hrow active hactive
  have hM := actual_flagged_mixed_L1 μ ν N hN row hrow target htarget active hactive p hp false
  have h0 := partial_private_L1 μ ν N hN row hrow private0 hprivate0 side 0
  have h1 := partial_private_L1 μ ν N hN row hrow private1 hprivate1 side 1
  rw [←hfair] at h1
  have hW := actual_flagged_reciprocal_L1 μ ν N hN row hrow target htarget active hactive p hp bid hbid
    1 (by norm_num) false
  have hi := integral_guardError_eq ν N (N+1) _ _ _ _
    (measurable_privateCount N row active hrow.measurable hactive)
    (measurable_flaggedMixedCount μ ν N row hrow target htarget active hactive p hp false)
    (measurable_partialPrivateCount μ ν N row hrow private0 hprivate0 side 0)
    (measurable_partialPrivateCount μ ν N row hrow private1 hprivate1 side 1)
    (fun x => (partial_counts_bounded N row target active private0 private1 p side x).1)
    (fun x => (partial_counts_bounded N row target active private0 private1 p side x).2.1)
    (fun x => (partial_counts_bounded N row target active private0 private1 p side x).2.2.1)
    (fun x => (partial_counts_bounded N row target active private0 private1 p side x).2.2.2)
    (flaggedReciprocal N row target active p bid 1 false)
    (integrable_flaggedReciprocal μ ν N hN row hrow target htarget active hactive p hp bid hbid 1 (by norm_num) false)
    (∫ x,indicator active x ∂μ) (∫ x,(p x:ℝ)*indicator active x ∂μ)
    (∫ x,indicator private0 x ∂μ) (∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ)
  change (∫ x,guardError N _ _ _ _ _ _ _ _ _ ∂ν) ≤ _
  rw [hi]
  have ho : (partialOffset side 0:ℝ)/N+(partialOffset side 1:ℝ)/N=1/(N:ℝ) := by
    rw [←add_div,partialOffset_sum]
  calc
    _ ≤ 1/Real.sqrt N + (1/Real.sqrt N + 1/(N:ℝ)) +
        (1/Real.sqrt N + (partialOffset side 0:ℝ)/N) +
        (1/Real.sqrt N + (partialOffset side 1:ℝ)/N) +
        (1/Real.sqrt N + 1/(N:ℝ)) + 1/(N:ℝ) :=
      add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hA hM) h0) h1) hW) (le_refl _)
    _ = _ := by linear_combination ho

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
include μ ν hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem measurable_partialGuardWeight (ξ share ρ B R Rp width : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg : Bool) (side : Fin 2) :
    Measurable (partialGuardWeight N row target active private0 private1 p bid
      ξ share ρ B R Rp width hshare reg side) :=
  measurable_scalarSourceWeight N _ _ _ _
    (measurable_privateCount N row active hrow.measurable hactive)
    (measurable_flaggedMixedCount μ ν N row hrow target htarget active hactive p hp false)
    (measurable_partialPrivateCount μ ν N row hrow private0 hprivate0 side 0)
    (measurable_partialPrivateCount μ ν N row hrow private1 hprivate1 side 1)
    ξ share ρ B R Rp width hshare reg _
    (measurable_flaggedReciprocal μ ν N row hrow target htarget active hactive p hp bid hbid 1 false)

include hN in
omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem partial_weight_eq_one_of_good (ξ share ρ B R Rp width γ δ : ℝ) (reg : Bool)
    (hξ : ξ∈Icc (0:ℝ) 1) (hshare : share∈Icc (0:ℝ) 1)
    (hshareLo : lowerShare reg≤ share) (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤ B)
    (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1) (hδ : 0< δ) :
    let abar := ∫ x,indicator active x ∂μ
    let mbar := ∫ x,(p x:ℝ)*indicator active x ∂μ
    let hbar := ∫ x,indicator private0 x ∂μ
    let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
    δ≤ mbar/2 → δ≤ wbar/2 → 4*δ≤ ρ-(abar-mbar)/2-hbar → 10*δ≤ γ*wbar →
    (1-ξ)*B+2*γ≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg)/wbar →
    populationNumerator ξ ρ abar mbar hbar 1/wbar+2*γ≤1 →
    (if reg then Rp+2*γ≤ populationNumerator ξ ρ abar mbar hbar share/wbar
      else populationNumerator ξ ρ abar mbar hbar share/wbar+2*γ≤ R) →
    ∀ side x,partialGuardError N row target active private0 private1 p bid abar mbar hbar wbar side x< δ →
      partialGuardWeight N row target active private0 private1 p bid ξ share ρ B R Rp width hshare reg side x=1 := by
  dsimp only
  intro hδm hδw hδc hδγ hlo hhi hmean side x hx
  let A := privateCount N row active x
  let M := flaggedMixedCount N row target active p false x
  let H0 := partialPrivateCount N row private0 side 0 x
  let H1 := partialPrivateCount N row private1 side 1 x
  have hhbar : 0≤∫ x,indicator private0 x ∂μ := integral_nonneg fun y => (indicator_bounds private0 y).1
  exact source_weight_eq_one_of_guardError N A M H0 H1 hN
    (partial_mixed_le_active N row target active p x)
    ξ share ρ B R Rp width γ δ (flaggedReciprocal N row target active p bid 1 false x)
    (∫ x,indicator active x ∂μ) (∫ x,(p x:ℝ)*indicator active x ∂μ)
    (∫ x,indicator private0 x ∂μ) (∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ) reg
    (guardMeanProxy H0 share hshare) (guardMeanProxy H1 share hshare)
    hξ hshare hshareLo hρ hB hhbar hw hwγ hγ1 hδ hδm hδw hδc hδγ
    (guardMeanProxy_mean H0 share hshare reg hshareLo) (guardMeanProxy_mean H1 share hshare reg hshareLo)
    hlo hhi hmean hx

include hN hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem original_partial_guard_failure (ξ share ρ B R Rp width γ δ : ℝ) (reg : Bool)
    (hξ : ξ∈Icc (0:ℝ) 1) (hshare : share∈Icc (0:ℝ) 1)
    (hshareLo : lowerShare reg≤ share) (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤ B)
    (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1) (hδ : 0< δ)
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
    ∀ side,ν.real {x | partialGuardWeight N row target active private0 private1 p bid
      ξ share ρ B R Rp width hshare reg side x≠1}≤(5/Real.sqrt N+4/(N:ℝ))/δ := by
  dsimp only
  intro hδm hδw hδc hδγ hlo hhi hmean side
  let G := partialGuardError N row target active private0 private1 p bid
    (∫ x,indicator active x ∂μ) (∫ x,(p x:ℝ)*indicator active x ∂μ)
    (∫ x,indicator private0 x ∂μ) (∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ) side
  let w := partialGuardWeight N row target active private0 private1 p bid ξ share ρ B R Rp width hshare reg side
  have hmeas : MeasurableSet {x | w x≠1} :=
    (measurableSet_eq_fun (measurable_partialGuardWeight μ ν N row hrow target htarget active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ B R Rp width hshare reg side) measurable_const).compl
  have hg (x : Ω) : 0≤ G x := (guardError_bounds N _ _ _ _ _ _ _ _ _).1
  have hpnt (x : Ω) : (if w x≠1 then (1:ℝ) else 0)≤ G x/δ := by
    by_cases hx : w x=1
    · simp only [hx,ne_eq,not_true_eq_false,ite_false]
      exact div_nonneg (hg x) hδ.le
    · simp only [hx,ne_eq,not_false_eq_true,ite_true]
      apply (le_div_iff₀ hδ).mpr
      have hn : ¬G x< δ := by
        intro hh
        exact hx (partial_weight_eq_one_of_good μ N hN row target active private0 private1 p bid
          ξ share ρ B R Rp width γ δ reg hξ hshare hshareLo hρ hB hw hwγ hγ1 hδ
          hδm hδw hδc hδγ hlo hhi hmean side x hh)
      simpa using le_of_not_gt hn
  have hiG := integrable_partialGuardError μ ν N hN row hrow target htarget active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid
    (∫ x,indicator active x ∂μ) (∫ x,(p x:ℝ)*indicator active x ∂μ)
    (∫ x,indicator private0 x ∂μ) (∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ) side
  have hi : Integrable (fun x => if w x≠1 then (1:ℝ) else 0) ν :=
    Integrable.of_bound (Measurable.ite hmeas measurable_const measurable_const).aestronglyMeasurable 1
      (ae_of_all _ (fun x => by split_ifs <;> norm_num))
  calc
    _ = ∫ x,if w x≠1 then (1:ℝ) else 0 ∂ν := by
      symm
      simpa only [Set.indicator,Set.mem_setOf_eq,Pi.one_apply] using integral_indicator_one (μ:=ν) hmeas
    _ ≤ ∫ x,G x/δ ∂ν := integral_mono_ae hi (hiG.div_const δ) (ae_of_all _ hpnt)
    _ = (∫ x,G x ∂ν)/δ := by simp only [div_eq_mul_inv,integral_mul_const]
    _ ≤ _ := div_le_div_of_nonneg_right
      (original_partial_guardError_L1 μ ν N hN row hrow target htarget active private0 private1
        hactive hprivate0 hprivate1 p hp bid hbid side hfair) hδ.le

end Original
end FCAppendix.Affine.Tail04.MenuError
