import FCAppendix.Affine.Tail04.TypicalGuardError

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open EqualPrivateSignal NativeTypicalCount TypicalGuardEndpoints

theorem scalarSourceWeight_defect_le (N A M H0 H1 : ℕ) (hN : 0< N) (hMA : M≤ A)
    (ξ share ρ B R Rp width γ δ W abar mbar hbar wbar : ℝ) (reg : Bool)
    (hξ : ξ∈Icc (0:ℝ) 1) (hshare : share∈Icc (0:ℝ) 1)
    (hshareLo : lowerShare reg≤ share) (hρ : ρ∈Icc (0:ℝ) 1)
    (hB : 0≤ B) (hhbar : 0≤ hbar) (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1)
    (hδ : 0< δ) (hδm : δ≤ mbar/2) (hδw : δ≤ wbar/2)
    (hδc : 4*δ≤ ρ-(abar-mbar)/2-hbar) (hδγ : 10*δ≤ γ*wbar)
    (hlo : (1-ξ)*B+2*γ≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg)/wbar)
    (hhi : populationNumerator ξ ρ abar mbar hbar 1/wbar+2*γ≤1)
    (hmean : if reg then Rp+2*γ≤ populationNumerator ξ ρ abar mbar hbar share/wbar
      else populationNumerator ξ ρ abar mbar hbar share/wbar+2*γ≤ R) :
    0≤1-scalarSourceWeight N A M H0 H1 ξ share ρ B R Rp width hshare reg W ∧
    1-scalarSourceWeight N A M H0 H1 ξ share ρ B R Rp width hshare reg W≤
      guardError N A M H0 H1 W abar mbar hbar wbar/δ := by
  have hb := scalarSourceWeight_bounds N A M H0 H1 ξ share ρ B R Rp width hshare reg W
  refine ⟨by linarith [hb.2],?_⟩
  by_cases hg : guardError N A M H0 H1 W abar mbar hbar wbar< δ
  · have he := source_weight_eq_one_of_guardError N A M H0 H1 hN hMA
      ξ share ρ B R Rp width γ δ W abar mbar hbar wbar reg
      (guardMeanProxy H0 share hshare) (guardMeanProxy H1 share hshare)
      hξ hshare hshareLo hρ hB hhbar hw hwγ hγ1 hδ hδm hδw hδc hδγ
      (guardMeanProxy_mean H0 share hshare reg hshareLo)
      (guardMeanProxy_mean H1 share hshare reg hshareLo) hlo hhi hmean hg
    change scalarSourceWeight N A M H0 H1 ξ share ρ B R Rp width hshare reg W=1 at he
    rw [he,sub_self]
    exact div_nonneg (guardError_bounds N A M H0 H1 W abar mbar hbar wbar).1 hδ.le
  · have he : 1≤ guardError N A M H0 H1 W abar mbar hbar wbar/δ :=
      (le_div_iff₀ hδ).mpr (by simpa using le_of_not_gt hg)
    linarith [hb.1]

section NumericIntegration
variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (N K : ℕ) (A M H0 H1 : Ω→ℕ)
variable (hA : Measurable A) (hM : Measurable M) (hH0 : Measurable H0) (hH1 : Measurable H1)
variable (hAK : ∀ x,A x≤ K) (hMK : ∀ x,M x≤ K) (h0K : ∀ x,H0 x≤ K) (h1K : ∀ x,H1 x≤ K)
variable (W : Ω→ℝ) (hW : Integrable W ν) (abar mbar hbar wbar : ℝ)

include K hA hM hH0 hH1 hAK hMK h0K h1K hW in
theorem integrable_guardError :
    Integrable (fun x => guardError N (A x) (M x) (H0 x) (H1 x) (W x) abar mbar hbar wbar) ν := by
  have hiA := (((integrable_bounded_nat ν A hA K hAK).div_const N).sub (integrable_const abar)).abs
  have hiM := (((integrable_bounded_nat ν M hM K hMK).div_const N).sub (integrable_const mbar)).abs
  have hi0 := (((integrable_bounded_nat ν H0 hH0 K h0K).div_const N).sub (integrable_const hbar)).abs
  have hi1 := (((integrable_bounded_nat ν H1 hH1 K h1K).div_const N).sub (integrable_const hbar)).abs
  exact ((((hiA.add hiM).add hi0).add hi1).add ((hW.sub (integrable_const wbar)).abs)).add
    (integrable_const (1/(N:ℝ)))

include K hA hM hH0 hH1 hAK hMK h0K h1K hW in
theorem integral_guardError_eq :
    (∫ x,guardError N (A x) (M x) (H0 x) (H1 x) (W x) abar mbar hbar wbar ∂ν)=
      (∫ x,|(A x:ℝ)/N-abar| ∂ν)+(∫ x,|(M x:ℝ)/N-mbar| ∂ν)+
      (∫ x,|(H0 x:ℝ)/N-hbar| ∂ν)+(∫ x,|(H1 x:ℝ)/N-hbar| ∂ν)+
      (∫ x,|W x-wbar| ∂ν)+1/(N:ℝ) := by
  have hiA := (((integrable_bounded_nat ν A hA K hAK).div_const N).sub (integrable_const abar)).abs
  have hiM := (((integrable_bounded_nat ν M hM K hMK).div_const N).sub (integrable_const mbar)).abs
  have hi0 := (((integrable_bounded_nat ν H0 hH0 K h0K).div_const N).sub (integrable_const hbar)).abs
  have hi1 := (((integrable_bounded_nat ν H1 hH1 K h1K).div_const N).sub (integrable_const hbar)).abs
  have hiW := (hW.sub (integrable_const wbar)).abs
  simp only [Pi.sub_apply] at hiA hiM hi0 hi1 hiW
  unfold guardError
  erw [integral_add ((((hiA.add hiM).add hi0).add hi1).add hiW) (integrable_const _),
    integral_add (((hiA.add hiM).add hi0).add hi1) hiW,
    integral_add ((hiA.add hiM).add hi0) hi1,
    integral_add (hiA.add hiM) hi0,integral_add hiA hiM]
  simp

include K hA hM hH0 hH1 hAK hMK h0K h1K hW in
theorem integrated_guardError
    (hEA : (∫ x,|(A x:ℝ)/N-abar| ∂ν)≤1/Real.sqrt N+1/(N:ℝ))
    (hEM : (∫ x,|(M x:ℝ)/N-mbar| ∂ν)≤1/Real.sqrt N+1/(N:ℝ))
    (hE0 : (∫ x,|(H0 x:ℝ)/N-hbar| ∂ν)≤1/Real.sqrt N)
    (hE1 : (∫ x,|(H1 x:ℝ)/N-hbar| ∂ν)≤1/Real.sqrt N)
    (hEW : (∫ x,|W x-wbar| ∂ν)≤1/Real.sqrt N+1/(N:ℝ)) :
    (∫ x,guardError N (A x) (M x) (H0 x) (H1 x) (W x) abar mbar hbar wbar ∂ν)≤
      5/Real.sqrt N+4/(N:ℝ) := by
  rw [integral_guardError_eq ν N K A M H0 H1 hA hM hH0 hH1 hAK hMK h0K h1K W hW]
  simp only [div_eq_mul_inv,one_mul] at hEA hEM hE0 hE1 hEW ⊢
  linarith

end NumericIntegration

section Definitions
variable {X Ω : Type*} (N : ℕ) (row : Ω→ Fin N→ X×unitInterval) (target : Ω→ Fin (N+1))
variable (active private0 private1 : X→ Bool) (p : X→ unitInterval) (bid : X→ℝ)

def originalGuardWeight (ξ share ρ B R Rp width b : ℝ) (hshare : share∈Icc (0:ℝ) 1)
    (reg : Bool) (x : Ω) : ℝ :=
  scalarSourceWeight N (activeCount N row active x) (mixedCount N row target active p x)
    (privateCount N row private0 x) (privateCount N row private1 x)
    ξ share ρ B R Rp width hshare reg (sourceReciprocal N row target active p bid b x)

def originalGuardError (b abar mbar hbar wbar : ℝ) (x : Ω) : ℝ :=
  guardError N (activeCount N row active x) (mixedCount N row target active p x)
    (privateCount N row private0 x) (privateCount N row private1 x)
    (sourceReciprocal N row target active p bid b x) abar mbar hbar wbar

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

include μ ν hrow htarget hactive hprivate0 hprivate1 hp hbid in
omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem measurable_originalGuardWeight (ξ share ρ B R Rp width b : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg : Bool) :
    Measurable (originalGuardWeight N row target active private0 private1 p bid
      ξ share ρ B R Rp width b hshare reg) :=
  measurable_scalarSourceWeight N _ _ _ _
    (measurable_activeCount N row active hrow.measurable hactive)
    (measurable_mixedCount N row target active p hrow.measurable htarget hactive hp)
    (measurable_privateCount N row private0 hrow.measurable hprivate0)
    (measurable_privateCount N row private1 hrow.measurable hprivate1)
    ξ share ρ B R Rp width hshare reg _
    (measurable_sourceReciprocal μ ν N row hrow target htarget active hactive p hp bid hbid b)

include μ hrow htarget hactive hprivate0 hprivate1 hp hbid in
omit [IsProbabilityMeasure μ] in
theorem integrable_originalGuardWeight (ξ share ρ B R Rp width b : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg : Bool) :
    Integrable (originalGuardWeight N row target active private0 private1 p bid
      ξ share ρ B R Rp width b hshare reg) ν := by
  apply Integrable.of_bound
    (measurable_originalGuardWeight μ ν N row hrow target htarget active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ B R Rp width b hshare reg).aestronglyMeasurable 1
  filter_upwards [] with x
  have hb := scalarSourceWeight_bounds N (activeCount N row active x)
    (mixedCount N row target active p x) (privateCount N row private0 x) (privateCount N row private1 x)
    ξ share ρ B R Rp width hshare reg (sourceReciprocal N row target active p bid b x)
  change ‖scalarSourceWeight N (activeCount N row active x)
    (mixedCount N row target active p x) (privateCount N row private0 x) (privateCount N row private1 x)
    ξ share ρ B R Rp width hshare reg (sourceReciprocal N row target active p bid b x)‖≤1
  rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
  exact hb.2

include μ hN hrow htarget hactive hprivate0 hprivate1 hp hbid in
omit [IsProbabilityMeasure μ] in
theorem integrable_originalGuardError (b abar mbar hbar wbar : ℝ) (hb : 1≤ b) :
    Integrable (originalGuardError N row target active private0 private1 p bid b abar mbar hbar wbar) ν := by
  apply integrable_guardError ν N (N+1) _ _ _ _
    (measurable_activeCount N row active hrow.measurable hactive)
    (measurable_mixedCount N row target active p hrow.measurable htarget hactive hp)
    (measurable_privateCount N row private0 hrow.measurable hprivate0)
    (measurable_privateCount N row private1 hrow.measurable hprivate1)
    (fun x => (source_count_bounds N row target active private0 private1 p x).1)
    (fun x => (source_count_bounds N row target active private0 private1 p x).2.1)
    (fun x => (source_count_bounds N row target active private0 private1 p x).2.2.1)
    (fun x => (source_count_bounds N row target active private0 private1 p x).2.2.2)
    (sourceReciprocal N row target active p bid b)
    (integrable_sourceReciprocal μ ν N hN row hrow target htarget active hactive p hp bid hbid b hb)

include hN hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem original_guardError_L1 (b : ℝ) (hb : 1≤ b)
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ)) :
    let abar := ∫ x,indicator active x ∂μ
    let mbar := ∫ x,(p x:ℝ)*indicator active x ∂μ
    let hbar := ∫ x,indicator private0 x ∂μ
    let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
    (∫ x,originalGuardError N row target active private0 private1 p bid b abar mbar hbar wbar x ∂ν)≤
      5/Real.sqrt N+4/(N:ℝ) := by
  dsimp only
  apply integrated_guardError ν N (N+1) _ _ _ _
    (measurable_activeCount N row active hrow.measurable hactive)
    (measurable_mixedCount N row target active p hrow.measurable htarget hactive hp)
    (measurable_privateCount N row private0 hrow.measurable hprivate0)
    (measurable_privateCount N row private1 hrow.measurable hprivate1)
    (fun x => (source_count_bounds N row target active private0 private1 p x).1)
    (fun x => (source_count_bounds N row target active private0 private1 p x).2.1)
    (fun x => (source_count_bounds N row target active private0 private1 p x).2.2.1)
    (fun x => (source_count_bounds N row target active private0 private1 p x).2.2.2)
    (sourceReciprocal N row target active p bid b)
    (integrable_sourceReciprocal μ ν N hN row hrow target htarget active hactive p hp bid hbid b hb)
  · exact actual_active_count_L1 μ ν N hN row hrow active hactive
  · exact actual_mixed_count_L1 μ ν N hN row hrow active hactive p hp target htarget
  · exact actual_private_count_L1 μ ν N hN row hrow private0 hprivate0
  · simpa only [←hfair] using actual_private_count_L1 μ ν N hN row hrow private1 hprivate1
  · exact actual_reciprocal_L1 μ ν N hN row hrow active hactive p hp bid hbid b hb target htarget

include hN hrow htarget hactive hprivate0 hprivate1 hp hbid in
theorem original_guard_defect_L1 (ξ share ρ B R Rp width γ δ b : ℝ) (reg : Bool)
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
    (∫ x,1-originalGuardWeight N row target active private0 private1 p bid
      ξ share ρ B R Rp width b hshare reg x ∂ν)≤(5/Real.sqrt N+4/(N:ℝ))/δ := by
  dsimp only
  intro hδm hδw hδc hδγ hlo hhi hmean
  let abar := ∫ x,indicator active x ∂μ
  let mbar := ∫ x,(p x:ℝ)*indicator active x ∂μ
  let hbar := ∫ x,indicator private0 x ∂μ
  let wbar := ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
  let Z := originalGuardError N row target active private0 private1 p bid b abar mbar hbar wbar
  have hhbar : 0≤ hbar := integral_nonneg fun x => (indicator_bounds private0 x).1
  have hpoint (x : Ω) : 1-originalGuardWeight N row target active private0 private1 p bid
      ξ share ρ B R Rp width b hshare reg x≤ Z x/δ :=
    (scalarSourceWeight_defect_le N (activeCount N row active x)
      (mixedCount N row target active p x) (privateCount N row private0 x) (privateCount N row private1 x)
      hN (mixedCount_le_activeCount N row target active p x)
      ξ share ρ B R Rp width γ δ (sourceReciprocal N row target active p bid b x)
      abar mbar hbar wbar reg hξ hshare hshareLo hρ hB hhbar hw hwγ hγ1 hδ
      hδm hδw hδc hδγ hlo hhi hmean).2
  have hiZ := integrable_originalGuardError μ ν N hN row hrow target htarget
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid b abar mbar hbar wbar hb
  have hiw := integrable_originalGuardWeight μ ν N row hrow target htarget
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid
    ξ share ρ B R Rp width b hshare reg
  calc
    _ ≤ ∫ x,Z x/δ ∂ν := integral_mono_ae ((integrable_const 1).sub hiw) (hiZ.div_const δ)
      (Eventually.of_forall hpoint)
    _ = (∫ x,Z x ∂ν)/δ := by simp only [div_eq_mul_inv,integral_mul_const]
    _ ≤ _ := div_le_div_of_nonneg_right
      (original_guardError_L1 μ ν N hN row hrow target htarget active private0 private1
        hactive hprivate0 hprivate1 p hp bid hbid b hb hfair) hδ.le

end OriginalLaw
end FCAppendix.Affine.Tail04.MenuError
