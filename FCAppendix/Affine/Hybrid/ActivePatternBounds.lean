import FCAppendix.Affine.Hybrid.ActivePatternGuards

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology Classical
open scoped BigOperators

lemma abs_finite_expect_le_of_support {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (f : Ω→ℝ) (C : ℝ) (h : ∀t,P.mass t≠0→|f t|≤C) : |P.expect f|≤C := by
  unfold FiniteLaw.expect
  calc
    _ ≤ ∑t,|P.mass t*f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑t,P.mass t*C := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : P.mass t=0
      · simp [ht]
      · rw [abs_mul,abs_of_nonneg (P.nonneg t)]
        exact mul_le_mul_of_nonneg_left (h t ht) (P.nonneg t)
    _ = C := by rw [←Finset.sum_mul,P.total,one_mul]

lemma abs_broadcastPayoff_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {eta : ℝ} (heta : |eta|≤1) (v bid : ℝ) (i : ι) (ST : Finset ι×Finset ι) :
    |broadcastPayoff eta v bid i ST|≤|v|+2*|bid| := by
  have hs : |(if i∈ST.1 ∨ i∈ST.2 then (1:ℝ) else 0)|≤1 := by split_ifs <;> norm_num
  have hd : |(if i∈ST.1 ∧ i∈ST.2 then (1:ℝ) else 0)|≤1 := by split_ifs <;> norm_num
  unfold broadcastPayoff
  calc
    _ ≤ |(v-bid)*(if i∈ST.1 ∨ i∈ST.2 then (1:ℝ) else 0)|+
        |eta*bid*(if i∈ST.1 ∧ i∈ST.2 then (1:ℝ) else 0)| := abs_sub _ _
    _ ≤ (|v|+|bid|)*1+1*|bid| *1 := by
      simp only [abs_mul]
      gcongr
      exact abs_sub _ _
    _ = _ := by ring

theorem abs_sourceOwnerPayoff_activePattern {N : ℕ} {xi L U eta : ℝ}
    (hxi : 0<xi) (hxi1 : xi<1) (hL : 0<L) (heta : |eta|≤1)
    (c : ℕ) (z : ℝ) (kind : Fin N→Fin 4) (hg : activePatternGuarded xi L U c z kind)
    (v : ℝ) (b : ActivePatternIndex kind→ℝ) (hb : ∀i,b i∈Icc L U) :
    |sourceOwnerPayoff xi eta v b (activePatternResidual c z kind)
      (activePatternOwner c z kind 0) (activePatternOwner c z kind 1) (activePatternFocal kind)|≤|v|+2*U := by
  unfold sourceOwnerPayoff
  apply abs_finite_expect_le_of_support
  intro E hE
  obtain ⟨Q,hqx,hqb,hq0,hq1,hqr,_hcap0,_hcap1⟩:=activePattern_guardedData hxi hxi1 hL c z kind hg b hb E.1 E.2 hE
  have he:=Q.expected_broadcastPayoff eta v (activePatternFocal kind)
  rw [hqx,hqb,hq0,hq1,hqr] at he
  rw [←he]
  apply abs_finite_expect_le_of_support
  intro ST _
  have hh:=abs_broadcastPayoff_le heta v (Q.bid (activePatternFocal kind)) (activePatternFocal kind) ST
  have hbid : |Q.bid (activePatternFocal kind)|≤U := by
    rw [hqb,abs_of_pos (hL.trans_le (hb _).1)]
    exact (hb _).2
  rw [hqb] at hh hbid
  exact hh.trans (show |v|+2*|b (activePatternFocal kind)|≤|v|+2*U from by linarith)

theorem abs_activePatternNoisyPayoff_le {N : ℕ} {d vlo vhi L U eps xi : ℝ}
    (hL : 0<L) (heps : 0≤eps) (hxi : 0<xi) (hxi1 : xi<1)
    (z : ℝ) (c : ℕ) (kind : Fin N→Fin 4) (t : ActivePatternInput N d vlo vhi L U eps)
    (noise : unitInterval) :
    |activePatternNoisyPayoff hL heps xi z c kind t noise|≤|(t.1.1:ℝ)|+3*(U*(1+eps)) := by
  have hB:=activeNoisyRealBid_mem hL heps t.1.2 noise
  have hpos : 0<activeNoisyRealBid eps t.1.2 noise:=hL.trans_le hB.1
  have hM : 0≤U*(1+eps):=hpos.le.trans hB.2
  have hown : |LowBody.noisyFocal (0:Fin (N+1)) eps (activePatternBids kind t) noise 0|≤U*(1+eps) := by
    change |activeNoisyRealBid eps t.1.2 noise|≤U*(1+eps)
    rw [abs_of_pos hpos]
    exact hB.2

  unfold activePatternNoisyPayoff
  dsimp only
  split_ifs with hg hequal
  · have heta : |1-2*xi|≤1:=abs_le.mpr ⟨by linarith,by linarith⟩
    have hh:=abs_sourceOwnerPayoff_activePattern hxi hxi1 hL heta c z kind hg
      (t.1.1:ℝ) (guardedNoisyInput eps (activePatternFocal kind)
        (activePatternGuardedInput hL heps kind t) noise).2
      (guardedNoisyInput_bid_mem hL heps _ _ noise)
    exact hh.trans (by linarith)
  · have hh:=LowBody.abs_equalPayoff_le hxi hxi1 (activePatternTemplate c kind).residual₀ 0
      (t.1.1:ℝ) (LowBody.noisyFocal 0 eps (activePatternBids kind t) noise)
    exact hh.trans (by linarith)
  · have hk : |1-xi|≤1:=by rw [abs_of_pos (by linarith : 0<1-xi)];linarith
    have hh:=LowBody.abs_purePayoff_le (1-xi) (t.1.1:ℝ)
      (LowBody.noisyFocal 0 eps (activePatternBids kind t) noise)
      ((activePatternTemplate c kind).selection (1-xi)
        (LowBody.noisyFocal 0 eps (activePatternBids kind t) noise)) 0
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hk (abs_nonneg
      (LowBody.noisyFocal (0:Fin (N+1)) eps (activePatternBids kind t) noise 0))])

theorem abs_activePatternSmoothedPayoff_le {N : ℕ} {d vlo vhi L U eps xi : ℝ}
    (hL : 0<L) (heps : 0≤eps) (hxi : 0<xi) (hxi1 : xi<1)
    (z : ℝ) (c : ℕ) (kind : Fin N→Fin 4) (t : ActivePatternInput N d vlo vhi L U eps) :
    |activePatternSmoothedPayoff hL heps xi z c kind t|≤|(t.1.1:ℝ)|+3*(U*(1+eps)) := by
  rw [activePatternSmoothedPayoff_eq_integral]
  have hb : ∀ᵐnoise : unitInterval ∂volume,
      ‖activePatternNoisyPayoff hL heps xi z c kind t noise‖≤|(t.1.1:ℝ)|+3*(U*(1+eps)) :=
    ae_of_all _ (fun noise=>by simpa only [Real.norm_eq_abs] using
      abs_activePatternNoisyPayoff_le hL heps hxi hxi1 z c kind t noise)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb

end FCAppendix.Affine.Hybrid
