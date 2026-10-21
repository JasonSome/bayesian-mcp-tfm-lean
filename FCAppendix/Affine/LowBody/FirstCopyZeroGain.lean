import FCAppendix.Affine.LowBody.FirstCopyNoisyGain
import FCAppendix.Affine.LowBody.ZeroClusterLoss

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
variable {N : ℕ}

lemma firstCopy_literalRowGain_small (c : ℕ) (hc : 0<c) {ξ w x z S Z u : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (hu : 0≤u)
    (omega : Fin N→RowRival) (r : RowRival)
    (hrow : ∀j : Fin (N+1),((Fin.cons r omega : Fin (N+1)→RowRival) j).1=0→
      0≤((Fin.cons r omega : Fin (N+1)→RowRival) j).2)
    (hx : 0≤x) (hxz : x≤z) (hzw : z≤w) (hzZ : z≤Z) (huz : u<z) (hS : S≤w-x) :
    (if omega∈firstCopyBoundary c u ∧ (x,r)∈firstCopyLowRejection c (1-ξ) u omega
      then S else 0)-2*Z≤literalRowPayoff ξ c w (z,Fin.cons r omega)-
        literalRowPayoff ξ c w (x,Fin.cons r omega) := by
  have hz : 0<z:=hu.trans_lt huz
  by_cases hb : omega∈firstCopyBoundary c u ∧ (x,r)∈firstCopyLowRejection c (1-ξ) u omega
  · rw [if_pos hb]
    have hh:=firstCopy_literalRowGain_bonus c hc ξ w 0 u x z S hu omega hb.1 r hb.2 hx huz hz hS
    linarith
  · rw [if_neg hb]
    have hh:=patternPayoff_small_bid_loss c hξ hξh (Fin.cons r omega) hx hxz hzw hrow
    linarith

section Carrier
variable {A : Type*} [MeasurableSpace A]

theorem firstCopy_zero_integrated_gain_lower {ξ : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G θ : Measure ℝ) [IsProbabilityMeasure G] [IsFiniteMeasure θ] [NullSingletonClass θ]
    (hθG : θ ≤ G) (hθ0 : θ univ≠0)
    (Γ : Measure A) [IsFiniteMeasure Γ]
    (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν]
    (c : ℕ) (hc : 0<c) (u S W Z : ℝ) (hu : 0≤u) (hS : 0≤S)
    (w x z : A→ℝ) (hw : Measurable w) (hx : Measurable x) (hz : Measurable z)
    (hpush : Γ.map x=θ) (hθ : ∀ᵐy ∂θ,y≤u)
    (hbox : ∀ᵐt ∂Γ,0≤x t ∧ x t≤z t ∧ z t≤w t ∧ z t≤Z ∧ u<z t ∧ S≤w t-x t ∧ |w t|≤W)
    (hrows : ∀ᵐq : (Fin N→RowRival)×(A×RowRival) ∂ν.prod (Γ.prod (rivalLaw s a h G)),
      ∀j : Fin (N+1),((Fin.cons q.2.2 q.1 : Fin (N+1)→RowRival) j).1=0→
        0≤((Fin.cons q.2.2 q.1 : Fin (N+1)→RowRival) j).2) :
    S*s*(Γ.real univ)^2*ν.real (firstCopyBoundary c u)/2-2*Z*Γ.real univ≤
      ∫q : (Fin N→RowRival)×(A×RowRival),
        literalRowPayoff ξ c (w q.2.1) (z q.2.1,Fin.cons q.2.2 q.1)-
          literalRowPayoff ξ c (w q.2.1) (x q.2.1,Fin.cons q.2.2 q.1)
            ∂ν.prod (Γ.prod (rivalLaw s a h G)) := by
  let ρ:=rivalLaw s a h G
  letI : IsProbabilityMeasure ρ:=rivalLaw_isProbability s a h hs ha hh hsum G
  let P:=ν.prod (Γ.prod ρ)
  let Bonus:=firstCopyCarrierBonus (N:=N) c (1-ξ) u x
  let F : (Fin N→RowRival)×(A×RowRival)→ℝ:=fun q=>
    literalRowPayoff ξ c (w q.2.1) (z q.2.1,Fin.cons q.2.2 q.1)-
      literalRowPayoff ξ c (w q.2.1) (x q.2.1,Fin.cons q.2.2 q.1)
  have hξ1 : ξ<1:=by linarith
  have hbounds : ∀ᵐt ∂Γ,|w t|≤W ∧ |x t|≤Z ∧ |z t|≤Z:=by
    filter_upwards [hbox] with t ht
    refine ⟨ht.2.2.2.2.2.2,?_,?_⟩
    · rw [abs_of_nonneg ht.1]
      exact ht.2.1.trans ht.2.2.2.1
    · rw [abs_of_nonneg (ht.1.trans ht.2.1)]
      exact ht.2.2.2.1
  have hFI : Integrable F P:=integrable_literalCarrierGain hξ hξ1 c ν Γ ρ w x z hw hx hz W Z Z hbounds
  have hBI : Integrable (Bonus.indicator (fun _=>S)) P:=
    (integrable_const S).indicator (measurableSet_firstCopyCarrierBonus c (1-ξ) u x hx)
  have hboxP:=(Measure.quasiMeasurePreserving_snd (μ:=ν) (ν:=Γ.prod ρ)).ae
    ((Measure.quasiMeasurePreserving_fst (μ:=Γ) (ν:=ρ)).ae hbox)
  have hpoint : ∀ᵐq ∂P,Bonus.indicator (fun _=>S) q-2*Z≤F q:=by
    filter_upwards [hboxP,hrows] with q hq hr
    have hh:=firstCopy_literalRowGain_small c hc hξ hξh hu q.1 q.2.2 hr
      hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2.1
    have hi : Bonus.indicator (fun _=>S) q=
        if q.1∈firstCopyBoundary c u ∧ (x q.2.1,q.2.2)∈firstCopyLowRejection c (1-ξ) u q.1
          then S else 0:=by
      simp only [Bonus,firstCopyCarrierBonus,Set.indicator,Set.mem_setOf_eq]
      rfl
    rw [hi]
    exact hh
  have hcompare:=integral_mono_ae (hBI.sub (integrable_const (2*Z))) hFI hpoint
  have hp : P.real univ=Γ.real univ:=by
    have hm₁ : P univ=(Γ.prod ρ) univ:=by
      simpa only [P,Set.univ_prod_univ,measure_univ,one_mul] using
        (Measure.prod_prod (μ:=ν) (ν:=Γ.prod ρ) univ univ)
    have hm₂ : (Γ.prod ρ) univ=Γ univ:=by
      simpa only [Set.univ_prod_univ,measure_univ,mul_one] using
        (Measure.prod_prod (μ:=Γ) (ν:=ρ) univ univ)
    exact congrArg ENNReal.toReal (hm₁.trans hm₂)
  change (∫q,Bonus.indicator (fun _=>S) q-2*Z ∂P)≤∫q,F q ∂P at hcompare
  rw [integral_sub hBI (integrable_const (2*Z))] at hcompare
  simp only [integral_const,smul_eq_mul,hp] at hcompare
  have hbonus:=firstCopy_actual_carrier_rejection_lower s a h hs ha hh hsum G θ hθG hθ0
    Γ x hx hpush c hc u (1-ξ) hu hθ ν
  have hbonus':=mul_le_mul_of_nonneg_left hbonus hS
  have hident:=integral_firstCopyCarrierBonus c (1-ξ) u S ν Γ ρ x hx
  change (∫q,Bonus.indicator (fun _=>S) q ∂P)=_ at hident
  rw [←hident] at hbonus'
  change _≤∫q,F q ∂P
  nlinarith

end Carrier
end FCAppendix.Affine.LowBody
