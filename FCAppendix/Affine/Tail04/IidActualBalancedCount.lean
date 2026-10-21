import FCAppendix.Affine.Tail04.IidBalancedCountError
import FCAppendix.Probability.FiniteAveraging

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators

section Definitions
variable {X Ω : Type*} (N : ℕ) (row : Ω→ Fin N→ X×unitInterval) (target : Ω→ Fin (N+1))
variable (active private0 private1 : X→ Bool) (p : X→ unitInterval) (bid : X→ℝ)
variable (ξ share ρ b : ℝ)

def sourceNumerator (x : Ω) (j : Fin 2) : ℝ :=
  countNumerator ξ share N (iidCapacity ρ N) (activeCount N row active x)
    (mixedCount N row target active p x) (privateCount N row private0 x) (privateCount N row private1 x) j

def sourceReciprocal (x : Ω) : ℝ :=
  forcedMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (1/b) row target x

def balancedCountExtension (x : Ω) : CountLaw 2 :=
  clippedCount ξ b (sourceNumerator N row target active private0 private1 p ξ share ρ x 0)
    (sourceNumerator N row target active private0 private1 p ξ share ρ x 1)
    (sourceReciprocal N row target active p bid b x)

theorem balancedCountExtension_eq_mean (hN : 0< N) (x : Ω) :
    let A := activeCount N row active x
    let M := mixedCount N row target active p x
    let H0 := privateCount N row private0 x
    let H1 := privateCount N row private1 x
    let Q := clampedOwner (A-M) (share*H0) (share*H1)
    balancedCountExtension N row target active private0 private1 p bid ξ share ρ b x=
      meanCountLaw ξ (iidCapacity ρ N) Q (A-M-Q) (share*H0) (share*H1) M
        ((N:ℝ)*sourceReciprocal N row target active p bid b x) b := by
  dsimp only
  have hn : (N:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [meanCountLaw_normalized ξ b N hn]
  simp [mul_div_cancel_left₀ _ hn,balancedCountExtension,sourceNumerator,countNumerator]

end Definitions

section OriginalLaw
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
include hrow htarget hactive hprivate0 hprivate1 hp in
theorem measurable_sourceNumerator (ξ share ρ : ℝ) (j : Fin 2) :
    Measurable (fun x => sourceNumerator N row target active private0 private1 p ξ share ρ x j) :=
  measurable_countNumerator ξ share N (iidCapacity ρ N) _ _ _ _
    (measurable_activeCount N row active hrow.measurable hactive)
    (measurable_mixedCount N row target active p hrow.measurable htarget hactive hp)
    (measurable_privateCount N row private0 hrow.measurable hprivate0)
    (measurable_privateCount N row private1 hrow.measurable hprivate1) j

omit [MeasurableSpace X] [MeasurableSpace Ω] in
theorem source_count_bounds (x : Ω) :
    activeCount N row active x≤ N+1 ∧ mixedCount N row target active p x≤ N+1 ∧
      privateCount N row private0 x≤ N+1 ∧ privateCount N row private1 x≤ N+1 := by
  have hA : activeCount N row active x ≤ N+1 := by
    simpa only [activeCount,privateCount,Fintype.card_fin] using
      (boolCount_le_card (Fin.cases true (fun i : Fin N => active (row x i).1)))
  have hM := (mixedCount_le_activeCount N row target active p x).trans hA
  have h0 : privateCount N row private0 x ≤ N := by
    simpa only [activeCount,privateCount,Fintype.card_fin] using
      (boolCount_le_card (fun i : Fin N => private0 (row x i).1))
  have h1 : privateCount N row private1 x ≤ N := by
    simpa only [activeCount,privateCount,Fintype.card_fin] using
      (boolCount_le_card (fun i : Fin N => private1 (row x i).1))
  exact ⟨hA,hM,h0.trans (Nat.le_succ _),h1.trans (Nat.le_succ _)⟩

omit [IsProbabilityMeasure μ] in
include hrow htarget hactive hprivate0 hprivate1 hp in
theorem integrable_sourceNumerator (ξ share ρ : ℝ) (j : Fin 2) :
    Integrable (fun x => sourceNumerator N row target active private0 private1 p ξ share ρ x j) ν :=
  integrable_countNumerator ν ξ share N (iidCapacity ρ N) (N+1) _ _ _ _
    (measurable_activeCount N row active hrow.measurable hactive)
    (measurable_mixedCount N row target active p hrow.measurable htarget hactive hp)
    (measurable_privateCount N row private0 hrow.measurable hprivate0)
    (measurable_privateCount N row private1 hrow.measurable hprivate1)
    (fun x => (source_count_bounds N row target active private0 private1 p x).1)
    (fun x => (source_count_bounds N row target active private0 private1 p x).2.1)
    (fun x => (source_count_bounds N row target active private0 private1 p x).2.2.1)
    (fun x => (source_count_bounds N row target active private0 private1 p x).2.2.2) j

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
include μ ν hrow htarget hactive hp hbid in
theorem measurable_sourceReciprocal (b : ℝ) :
    Measurable (sourceReciprocal N row target active p bid b) :=
  measurable_forcedMean (μ.prod (volume : Measure unitInterval)) ν N row hrow
    (Empirical.markedStatistic p (reciprocalWeight active bid))
    (Empirical.measurable_markedStatistic p hp (reciprocalWeight active bid)
      (measurable_reciprocalWeight active hactive bid hbid)) (1/b) target htarget

omit [IsProbabilityMeasure μ] in
include μ hN hrow htarget hactive hp hbid in
theorem integrable_sourceReciprocal (b : ℝ) (hb : 1≤ b) :
    Integrable (sourceReciprocal N row target active p bid b) ν := by
  have hb0 : 0< b := lt_of_lt_of_le (by norm_num) hb
  exact integrable_forcedMean (μ.prod (volume : Measure unitInterval)) ν N hN row hrow
    (Empirical.markedStatistic p (reciprocalWeight active bid))
    (Empirical.measurable_markedStatistic p hp (reciprocalWeight active bid)
      (measurable_reciprocalWeight active hactive bid hbid))
    (Empirical.markedStatistic_bounds p (reciprocalWeight active bid) (reciprocalWeight_bounds active bid))
    (1/b) ⟨div_nonneg (by norm_num) hb0.le,(div_le_one hb0).mpr hb⟩ target htarget

include hN hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem original_balanced_count_L1 (ξ share ρ b : ℝ)
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hshare : 0≤ share) (hρ : ρ∈Icc (0:ℝ) 1) (hb : 1≤ b)
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ))
    (f : Fin 3→ℝ) :
    let abar := ∫ x,indicator active x ∂μ
    let mbar := ∫ x,(p x:ℝ)*indicator active x ∂μ
    let hbar := ∫ x,indicator private0 x ∂μ
    let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
    let nbar := (1-ξ/2)*mbar-ξ*ρ+(ξ/2)*abar+ξ*share*hbar
    0< wbar → |nbar|≤ wbar →
      (∫ x,|(balancedCountExtension N row target active private0 private1 p bid ξ share ρ b x).expect f-
        (clippedCount ξ b nbar nbar wbar).expect f| ∂ν)≤
      oscillation f*((4/(ξ*b*wbar))*(numeratorBudget ξ share N+1/Real.sqrt N+1/(N:ℝ))+
        (4/wbar)*(1/Real.sqrt N+1/(N:ℝ))) := by
  dsimp only
  intro hwbar hnbar
  let abar := ∫ x,indicator active x ∂μ
  let mbar := ∫ x,(p x:ℝ)*indicator active x ∂μ
  let hbar := ∫ x,indicator private0 x ∂μ
  let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
  let nbar := (1-ξ/2)*mbar-ξ*ρ+(ξ/2)*abar+ξ*share*hbar
  have hA := measurable_activeCount N row active hrow.measurable hactive
  have hM := measurable_mixedCount N row target active p hrow.measurable htarget hactive hp
  have hH0 := measurable_privateCount N row private0 hrow.measurable hprivate0
  have hH1 := measurable_privateCount N row private1 hrow.measurable hprivate1
  have hn (j : Fin 2) :
      (∫ x,|sourceNumerator N row target active private0 private1 p ξ share ρ x j-nbar| ∂ν)≤
        numeratorBudget ξ share N := by
    apply numerator_L1_of_counts ν ξ share ρ hξ.le hξ1 hshare hρ N hN _ _ _ _ hA hM hH0 hH1
      (fun x => (source_count_bounds N row target active private0 private1 p x).1)
      (fun x => (source_count_bounds N row target active private0 private1 p x).2.1)
      (fun x => (source_count_bounds N row target active private0 private1 p x).2.2.1)
      (fun x => (source_count_bounds N row target active private0 private1 p x).2.2.2)
      (mixedCount_le_activeCount N row target active p) abar mbar hbar _ _ _ _ j
    · exact actual_active_count_L1 μ ν N hN row hrow active hactive
    · exact actual_mixed_count_L1 μ ν N hN row hrow active hactive p hp target htarget
    · exact actual_private_count_L1 μ ν N hN row hrow private0 hprivate0
    · simpa only [←hfair] using actual_private_count_L1 μ ν N hN row hrow private1 hprivate1
  have hrecip := actual_reciprocal_L1 μ ν N hN row hrow active hactive p hp bid hbid b hb target htarget
  have hmn (j : Fin 2) := measurable_sourceNumerator μ ν N row hrow target htarget
    active private0 private1 hactive hprivate0 hprivate1 p hp ξ share ρ j
  have hin (j : Fin 2) := integrable_sourceNumerator μ ν N row hrow target htarget
    active private0 private1 hactive hprivate0 hprivate1 p hp ξ share ρ j
  have hmw := measurable_sourceReciprocal μ ν N row hrow target htarget active hactive p hp bid hbid b
  have hiw := integrable_sourceReciprocal μ ν N hN row hrow target htarget active hactive p hp bid hbid b hb
  have he := integrated_clippedCount_error ν f ξ b nbar wbar
    (numeratorBudget ξ share N) (numeratorBudget ξ share N) (1/Real.sqrt N+1/(N:ℝ))
    (fun x => sourceNumerator N row target active private0 private1 p ξ share ρ x 0)
    (fun x => sourceNumerator N row target active private0 private1 p ξ share ρ x 1)
    (sourceReciprocal N row target active p bid b) (hmn 0) (hmn 1) hmw (hin 0) (hin 1) hiw
    hξ (lt_of_lt_of_le (by norm_num) hb) hwbar hnbar (hn 0) (hn 1) hrecip
  convert! he using 1
  ring

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
include μ ν hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem measurable_balancedCount_mass (ξ share ρ b : ℝ) (r : Fin 3) :
    Measurable (fun x =>
      (balancedCountExtension N row target active private0 private1 p bid ξ share ρ b x).mass r) := by
  have hmn (j : Fin 2) := measurable_sourceNumerator μ ν N row hrow target htarget
    active private0 private1 hactive hprivate0 hprivate1 p hp ξ share ρ j
  have hmw := measurable_sourceReciprocal μ ν N row hrow target htarget active hactive p hp bid hbid b
  have hh := measurable_clippedCount_expect ξ b
    (fun x => sourceNumerator N row target active private0 private1 p ξ share ρ x 0)
    (fun x => sourceNumerator N row target active private0 private1 p ξ share ρ x 1)
    (sourceReciprocal N row target active p bid b) (hmn 0) (hmn 1) hmw
    (fun k => if k=r then (1:ℝ) else 0)
  simpa only [FiniteLaw.expect_singleton, balancedCountExtension] using hh

def originalBalancedCount (ξ share ρ b : ℝ) : CountLaw 2 :=
  FiniteLaw.average ν
    (balancedCountExtension N row target active private0 private1 p bid ξ share ρ b)
    (measurable_balancedCount_mass μ ν N row hrow target htarget active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ b)

omit [IsProbabilityMeasure μ] in
theorem originalBalancedCount_expect (ξ share ρ b : ℝ) (f : Fin 3→ℝ) :
    (originalBalancedCount μ ν N row hrow target htarget active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ b).expect f=
      ∫ x,(balancedCountExtension N row target active private0 private1 p bid ξ share ρ b x).expect f ∂ν :=
  FiniteLaw.expect_average ν _ _ f

include hN in
theorem original_balanced_count_error (ξ share ρ b : ℝ)
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hshare : 0≤ share) (hρ : ρ∈Icc (0:ℝ) 1) (hb : 1≤ b)
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ))
    (f : Fin 3→ℝ) :
    let abar := ∫ x,indicator active x ∂μ
    let mbar := ∫ x,(p x:ℝ)*indicator active x ∂μ
    let hbar := ∫ x,indicator private0 x ∂μ
    let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
    let nbar := (1-ξ/2)*mbar-ξ*ρ+(ξ/2)*abar+ξ*share*hbar
    0< wbar → |nbar|≤ wbar →
      |(originalBalancedCount μ ν N row hrow target htarget active private0 private1
        hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ b).expect f-
        (clippedCount ξ b nbar nbar wbar).expect f|≤
      oscillation f*((4/(ξ*b*wbar))*(numeratorBudget ξ share N+1/Real.sqrt N+1/(N:ℝ))+
        (4/wbar)*(1/Real.sqrt N+1/(N:ℝ))) := by
  dsimp only
  intro hwbar hnbar
  let nbar := (1-ξ/2)*(∫ x,(p x:ℝ)*indicator active x ∂μ)-ξ*ρ+
    (ξ/2)*(∫ x,indicator active x ∂μ)+ξ*share*(∫ x,indicator private0 x ∂μ)
  let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
  have hmeas := measurable_balancedCount_mass μ ν N row hrow target htarget
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ b
  have hi := FiniteLaw.integrable_expect ν
    (balancedCountExtension N row target active private0 private1 p bid ξ share ρ b) hmeas f
  have he :
      |(originalBalancedCount μ ν N row hrow target htarget active private0 private1
          hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ b).expect f-
        (clippedCount ξ b nbar nbar wbar).expect f|=
      |∫ x,(balancedCountExtension N row target active private0 private1 p bid ξ share ρ b x).expect f-
        (clippedCount ξ b nbar nbar wbar).expect f ∂ν| := by
    rw [originalBalancedCount_expect,integral_sub hi (integrable_const _)]
    simp only [integral_const,probReal_univ,one_smul]
  rw [he]
  have hn :
      |∫ x,(balancedCountExtension N row target active private0 private1 p bid ξ share ρ b x).expect f-
        (clippedCount ξ b nbar nbar wbar).expect f ∂ν|≤
      ∫ x,|(balancedCountExtension N row target active private0 private1 p bid ξ share ρ b x).expect f-
        (clippedCount ξ b nbar nbar wbar).expect f| ∂ν := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x =>
      (balancedCountExtension N row target active private0 private1 p bid ξ share ρ b x).expect f-
        (clippedCount ξ b nbar nbar wbar).expect f)
  exact hn.trans (original_balanced_count_L1 μ ν N hN row hrow target htarget active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ b hξ hξ1 hshare hρ hb hfair f hwbar hnbar)

end OriginalLaw

def affineStatistic (η v b : ℝ) : Fin 3→ℝ := ![0,v-b,v-(1+η)*b]

theorem affineStatistic_userPayoff (η v b : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (G : Schedule 2) (r : Fin 3) :
    affineStatistic η v b r=userPayoff v b 0 (Schedule.affine 2 η hη0 hη1).charge G.charge r.val := by
  fin_cases r <;> simp [affineStatistic,userPayoff,successIndicator,Schedule.affine]
  ring

theorem affineStatistic_utility (C : CountLaw 2) (η v b : ℝ)
    (hη0 : 0≤ η) (hη1 : η≤1) (G : Schedule 2) :
    C.expect (affineStatistic η v b)=C.utility v b 0 (Schedule.affine 2 η hη0 hη1) G := by
  apply C.expect_congr
  exact affineStatistic_userPayoff η v b hη0 hη1 G

theorem oscillation_affineStatistic {η v b : ℝ} (hη0 : 0≤ η) (hη1 : η≤1)
    (hv : 0≤ v) (hb : 0≤ b) : oscillation (affineStatistic η v b)≤ v+b := by
  change max |(v-b)-0| |(v-(1+η)*b)-(v-b)|≤ v+b
  rw [sub_zero]
  apply max_le
  · exact abs_le.mpr ⟨by linarith,by linarith⟩
  · have he : (v-(1+η)*b)-(v-b)=-(η*b) := by ring
    rw [he,abs_neg,abs_of_nonneg (mul_nonneg hη0 hb)]
    exact (mul_le_of_le_one_left hb hη1).trans (by linarith)

end FCAppendix.Affine.Tail04.MenuError
