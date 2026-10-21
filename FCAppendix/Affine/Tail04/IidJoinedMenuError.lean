import FCAppendix.Affine.Tail04.IidTypicalGuard
import FCAppendix.Affine.Tail04.OriginalOwnerCount

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon NativeTypicalCount

theorem count_statistic_center_bound (f : Fin 3→ℝ) (k : Fin 3) :
    |f k-f 1|≤ oscillation f := by
  have hk : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hk with hk | hk | hk <;> subst k
  · rw [abs_sub_comm (f 0) (f 1)]
    exact le_max_left _ _
  · simpa using oscillation_nonneg f
  · exact le_max_right _ _

theorem count_expect_center_bound (C : CountLaw 2) (f : Fin 3→ℝ) :
    |C.expect f-f 1|≤ oscillation f := by
  have hl : f 1-oscillation f≤ C.expect f :=
    C.const_le_expect fun k => by linarith [(abs_le.mp (count_statistic_center_bound f k)).1]
  have hu : C.expect f≤ f 1+oscillation f :=
    C.expect_le_const fun k => by linarith [(abs_le.mp (count_statistic_center_bound f k)).2]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem count_expect_difference_bound (C D : CountLaw 2) (f : Fin 3→ℝ) :
    |C.expect f-D.expect f|≤2*oscillation f := by
  have hc := count_expect_center_bound C f
  have hd := count_expect_center_bound D f
  have ht := abs_sub_le (C.expect f) (f 1) (D.expect f)
  rw [abs_sub_comm (f 1)] at ht
  linarith

theorem joined_count_defect (C fallback : CountLaw 2) (f : Fin 3→ℝ)
    (w : ℝ) (hw0 : 0≤ w) (hw1 : w≤1) :
    |(FiniteLaw.mixture C fallback w hw0 hw1).expect f-C.expect f|≤
      2*oscillation f*(1-w) := by
  rw [FiniteLaw.expect_mixture]
  have he : w*C.expect f+(1-w)*fallback.expect f-C.expect f=
      (1-w)*(fallback.expect f-C.expect f) := by ring
  rw [he,abs_mul,abs_of_nonneg (by linarith : 0≤1-w)]
  have hh := mul_le_mul_of_nonneg_left (count_expect_difference_bound fallback C f)
    (by linarith : 0≤1-w)
  convert! hh using 1; ring

theorem joined_count_error (C fallback ideal : CountLaw 2) (f : Fin 3→ℝ)
    (w : ℝ) (hw0 : 0≤ w) (hw1 : w≤1) :
    |(FiniteLaw.mixture C fallback w hw0 hw1).expect f-ideal.expect f|≤
      |C.expect f-ideal.expect f|+2*oscillation f*(1-w) := by
  have ht := abs_sub_le ((FiniteLaw.mixture C fallback w hw0 hw1).expect f)
    (C.expect f) (ideal.expect f)
  linarith [joined_count_defect C fallback f w hw0 hw1]

theorem native_joined_count_defect (N H0 H1 c : ℕ) {ξ B : ℝ} (R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hw : 0< width)
    (p : JoinedHighPolicy.Parameters N H0 R Rp B)
    (θ0 : Measure (EqualPrivateUpper.Row H0 R Rp Rm))
    (θ1 : Measure (EqualPrivateUpper.Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hν0 : θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0)
    (hν1 : θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1)
    (hell0 : (JoinedHighPolicy.owner0 p.1.1).card=
      (countParameters N H0 H1 c ξ (JoinedHighPolicy.regime p.1.1) ν0 ν1).owner0
        (JoinedHighPolicy.mixed p.1.1).card)
    (hell1 : (JoinedHighPolicy.owner1 p.1.1).card=
      (countParameters N H0 H1 c ξ (JoinedHighPolicy.regime p.1.1) ν0 ν1).owner1
        (JoinedHighPolicy.mixed p.1.1).card)
    (i : Fin N) (f : Fin 3→ℝ) :
    |(originalJoinedCountLaw N H0 H1 c ξ B R Rp Rm width ν0 ν1 p θ0 θ1 i).expect f-
      (if i∈JoinedHighPolicy.mixed p.1.1 then
        (countParameters N H0 H1 c ξ (JoinedHighPolicy.regime p.1.1) ν0 ν1).mixedCount
          (JoinedHighPolicy.mixed p.1.1).card
          (mixedReciprocalSum (JoinedHighPolicy.mixed p.1.1) (JoinedHighPolicy.publicBids p))
          (JoinedHighPolicy.publicBids p i)
      else FiniteLaw.dirac 1).expect f|≤
      2*oscillation f*(1-(weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p:ℝ)) := by
  rw [originalJoinedCountLaw_balanced N H0 H1 c R Rp Rm width ν0 ν1
    hξ hξ1 hw p θ0 θ1 hν0 hν1 hell0 hell1 i]
  exact joined_count_defect _ _ f _ _ _

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

def guardedBalancedCount (ξ share ρ B R Rp width b : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg : Bool) (fallback : Ω→ CountLaw 2) (x : Ω) : CountLaw 2 :=
  FiniteLaw.mixture
    (balancedCountExtension N row target active private0 private1 p bid ξ share ρ b x) (fallback x)
    (originalGuardWeight N row target active private0 private1 p bid ξ share ρ B R Rp width b hshare reg x)
    (scalarSourceWeight_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1
    (scalarSourceWeight_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2

include μ ν hrow htarget hactive hprivate0 hprivate1 hp hbid in
omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem measurable_guardedBalancedCount_mass (ξ share ρ B R Rp width b : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg : Bool) (fallback : Ω→ CountLaw 2)
    (hfallback : ∀ k,Measurable (fun x => (fallback x).mass k)) (k : Fin 3) :
    Measurable (fun x => (guardedBalancedCount N row target active private0 private1 p bid
      ξ share ρ B R Rp width b hshare reg fallback x).mass k) := by
  have hw := measurable_originalGuardWeight μ ν N row hrow target htarget active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ B R Rp width b hshare reg
  have hc := measurable_balancedCount_mass μ ν N row hrow target htarget active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ b k
  exact (hw.mul hc).add ((measurable_const.sub hw).mul (hfallback k))

def originalGuardedBalancedCount (ξ share ρ B R Rp width b : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg : Bool) (fallback : Ω→ CountLaw 2)
    (hfallback : ∀ k,Measurable (fun x => (fallback x).mass k)) : CountLaw 2 :=
  FiniteLaw.average ν
    (guardedBalancedCount N row target active private0 private1 p bid
      ξ share ρ B R Rp width b hshare reg fallback)
    (measurable_guardedBalancedCount_mass μ ν N row hrow target htarget active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ B R Rp width b hshare reg fallback hfallback)

include hN in
theorem original_guarded_count_error (ξ share ρ B R Rp width γ δ b : ℝ) (reg : Bool)
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hshare : share∈Icc (0:ℝ) 1)
    (hshareLo : lowerShare reg≤ share) (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤ B)
    (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1) (hδ : 0< δ) (hb : 1≤ b)
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ))
    (fallback : Ω→ CountLaw 2) (hfallback : ∀ k,Measurable (fun x => (fallback x).mass k))
    (f : Fin 3→ℝ) :
    let abar := ∫ x,indicator active x ∂μ
    let mbar := ∫ x,(p x:ℝ)*indicator active x ∂μ
    let hbar := ∫ x,indicator private0 x ∂μ
    let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
    let nbar := populationNumerator ξ ρ abar mbar hbar share
    δ≤ mbar/2 → δ≤ wbar/2 → 4*δ≤ ρ-(abar-mbar)/2-hbar → 10*δ≤ γ*wbar →
    (1-ξ)*B+2*γ≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg)/wbar →
    populationNumerator ξ ρ abar mbar hbar 1/wbar+2*γ≤1 →
    (if reg then Rp+2*γ≤ nbar/wbar else nbar/wbar+2*γ≤ R) →
    |(originalGuardedBalancedCount μ ν N row hrow target htarget active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ B R Rp width b hshare reg fallback hfallback).expect f-
      (clippedCount ξ b nbar nbar wbar).expect f|≤
      oscillation f*((4/(ξ*b*wbar))*(numeratorBudget ξ share N+1/Real.sqrt N+1/(N:ℝ))+
        (4/wbar)*(1/Real.sqrt N+1/(N:ℝ))+2*((5/Real.sqrt N+4/(N:ℝ))/δ)) := by
  dsimp only
  intro hδm hδw hδc hδγ hlo hhi hmean
  let abar := ∫ x,indicator active x ∂μ
  let mbar := ∫ x,(p x:ℝ)*indicator active x ∂μ
  let hbar := ∫ x,indicator private0 x ∂μ
  let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
  let nbar := populationNumerator ξ ρ abar mbar hbar share
  let ideal := clippedCount ξ b nbar nbar wbar
  let C := balancedCountExtension N row target active private0 private1 p bid ξ share ρ b
  let J := guardedBalancedCount N row target active private0 private1 p bid
    ξ share ρ B R Rp width b hshare reg fallback
  let w := originalGuardWeight N row target active private0 private1 p bid
    ξ share ρ B R Rp width b hshare reg
  have hwbar : 0< wbar := by linarith
  have hγ : 0< γ := hw.trans_le hwγ
  have hhbar : 0≤ hbar := integral_nonneg fun x => (indicator_bounds private0 x).1
  have hκB : 0≤(1-ξ)*B := mul_nonneg (by linarith) hB
  have hnlo : 0≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg) := by
    have hh : 0≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg)/wbar := by linarith
    simpa using (le_div_iff₀ hwbar).mp hh
  have hnhi : populationNumerator ξ ρ abar mbar hbar 1≤ wbar := by
    have hh : populationNumerator ξ ρ abar mbar hbar 1/wbar≤1 := by linarith
    simpa using (div_le_iff₀ hwbar).mp hh
  have hnbar : |nbar|≤ wbar := by
    have hlo' := populationNumerator_mono (ρ:=ρ) (abar:=abar) (mbar:=mbar) hξ.le hhbar hshareLo
    have hhi' := populationNumerator_mono (ρ:=ρ) (abar:=abar) (mbar:=mbar) hξ.le hhbar hshare.2
    rw [abs_of_nonneg (hnlo.trans hlo')]
    exact hhi'.trans hnhi
  have hnbar_eq : nbar=(1-ξ/2)*mbar-ξ*ρ+(ξ/2)*abar+ξ*share*hbar := by
    dsimp [nbar,populationNumerator]
    ring
  have hmeanrate := original_balanced_count_L1 μ ν N hN row hrow target htarget active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ b hξ hξ1 hshare.1 hρ hb hfair f hwbar
    (hnbar_eq ▸ hnbar)
  rw [←hnbar_eq] at hmeanrate
  have hweightrate := original_guard_defect_L1 μ ν N hN row hrow target htarget
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid
    ξ share ρ B R Rp width γ δ b reg ⟨hξ.le,hξ1⟩ hshare hshareLo hρ hB
    hw hwγ hγ1 hδ hb hfair hδm hδw hδc hδγ hlo hhi hmean
  have hJ := measurable_guardedBalancedCount_mass μ ν N row hrow target htarget
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid
    ξ share ρ B R Rp width b hshare reg fallback hfallback
  have hC := measurable_balancedCount_mass μ ν N row hrow target htarget
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ b
  have hiJ := FiniteLaw.integrable_expect ν J hJ f
  have hiC := FiniteLaw.integrable_expect ν C hC f
  have hiw := integrable_originalGuardWeight μ ν N row hrow target htarget
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid
    ξ share ρ B R Rp width b hshare reg
  have hip : Integrable (fun x => |(C x).expect f-ideal.expect f|) ν :=
    (hiC.sub (integrable_const _)).abs
  have hid : Integrable (fun x => 2*oscillation f*(1-w x)) ν :=
    ((integrable_const 1).sub hiw).const_mul _
  have hpoint (x : Ω) : |(J x).expect f-ideal.expect f|≤
      |(C x).expect f-ideal.expect f|+2*oscillation f*(1-w x) :=
    joined_count_error _ _ _ f _ _ _
  have havg : (originalGuardedBalancedCount μ ν N row hrow target htarget active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ B R Rp width b hshare reg fallback hfallback).expect f-
      ideal.expect f=(∫ x,(J x).expect f-ideal.expect f ∂ν) := by
    rw [originalGuardedBalancedCount,FiniteLaw.expect_average]
    change (∫ x,(J x).expect f ∂ν)-ideal.expect f=_
    rw [integral_sub hiJ (integrable_const _)]
    simp
  rw [havg]
  have hnorm : |∫ x,(J x).expect f-ideal.expect f ∂ν|≤
      ∫ x,|(J x).expect f-ideal.expect f| ∂ν := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun x => (J x).expect f-ideal.expect f)
  have hbnd := integral_mono_ae ((hiJ.sub (integrable_const _)).abs) (hip.add hid)
    (Eventually.of_forall hpoint)
  simp only [Pi.add_apply,Pi.sub_apply] at hbnd
  erw [integral_add hip hid,integral_const_mul] at hbnd
  change (∫ x,1-w x ∂ν)≤_ at hweightrate
  change (∫ x,|(C x).expect f-ideal.expect f| ∂ν)≤_ at hmeanrate
  have hco : (0:ℝ)≤2*oscillation f := mul_nonneg (by norm_num) (oscillation_nonneg f)
  have hw' := mul_le_mul_of_nonneg_left hweightrate hco
  have hr := hnorm.trans hbnd
  nlinarith [hmeanrate,hw']

end OriginalLaw

theorem masked_favored_count_error (C fallback ideal : CountLaw 2) (f : Fin 3→ℝ)
    (enabled mixed favored : Bool) (w : ℝ) (hw0 : 0≤ w) (hw1 : w≤1) :
    let actual := if enabled then FiniteLaw.mixture
      (if mixed && !favored then C else FiniteLaw.dirac 1) fallback w hw0 hw1 else fallback
    let benchmark := if mixed then ideal else FiniteLaw.dirac 1
    |actual.expect f-benchmark.expect f|≤
      |C.expect f-ideal.expect f|+2*oscillation f*
        ((1-w)+(if enabled then 0 else 1)+(if favored then 1 else 0)) := by
  dsimp only
  have ho := oscillation_nonneg f
  have hw : 0≤1-w := by linarith
  cases enabled
  · simp only [Bool.false_eq_true,ite_false]
    have hh := count_expect_difference_bound fallback
      (if mixed then ideal else FiniteLaw.dirac 1) f
    cases favored <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
      nlinarith [abs_nonneg (C.expect f-ideal.expect f)]
  · simp only [ite_true]
    cases mixed
    · simp only [Bool.false_and,Bool.false_eq_true,ite_false]
      have hh := joined_count_defect (FiniteLaw.dirac 1) fallback f w hw0 hw1
      cases favored <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
        nlinarith [abs_nonneg (C.expect f-ideal.expect f)]
    · simp only [ite_true,Bool.true_and]
      cases favored
      · simpa using joined_count_error C fallback ideal f w hw0 hw1
      · simp only [Bool.not_true,Bool.false_eq_true,ite_false]
        have hh := count_expect_difference_bound
          (FiniteLaw.mixture (FiniteLaw.dirac 1) fallback w hw0 hw1) ideal f
        simp only [ite_true]
        nlinarith [abs_nonneg (C.expect f-ideal.expect f)]

end FCAppendix.Affine.Tail04.MenuError
