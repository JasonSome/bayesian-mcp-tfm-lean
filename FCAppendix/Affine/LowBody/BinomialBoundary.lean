import FCAppendix.Probability.PiBinomial
import FCAppendix.Probability.TriangularCramerRows
import FCAppendix.Ample.RateSystem

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

lemma pmf_adjacent (N k : ℕ) (p : ℝ) (hk : k<N) :
    ((k+1:ℕ):ℝ)*(1-p)*PiBinomial.pmf N p (k+1)=
      ((N-k:ℕ):ℝ)*p*PiBinomial.pmf N p k := by
  have hc : (N.choose (k+1):ℝ)*((k+1:ℕ):ℝ)=(N.choose k:ℝ)*((N-k:ℕ):ℝ) :=
    by exact_mod_cast Nat.choose_succ_right_eq N k
  have he : N-k=(N-(k+1))+1 := by omega
  have hh := congrArg (fun x : ℝ=>x*p^(k+1)*(1-p)^((N-(k+1))+1)) hc
  simp only [pow_succ] at hh
  unfold PiBinomial.pmf
  rw [he] at hh ⊢
  simp only [pow_succ]
  nlinarith only [hh]

lemma pmf_le_next (N k : ℕ) (p : ℝ) (hp0 : 0≤p) (hp1 : p<1)
    (hk : k<N) (hmode : ((k+1:ℕ):ℝ)≤((N+1:ℕ):ℝ)*p) :
    PiBinomial.pmf N p k≤PiBinomial.pmf N p (k+1) := by
  have he := pmf_adjacent N k p hk
  have hNp : ((N-k:ℕ):ℝ)=(N:ℝ)-(k:ℝ) := Nat.cast_sub hk.le
  have hkR : ((k+1:ℕ):ℝ)=(k:ℝ)+1 := Nat.cast_add_one k
  have hNR : ((N+1:ℕ):ℝ)=(N:ℝ)+1 := Nat.cast_add_one N
  rw [hNp,hkR] at he
  rw [hkR,hNR] at hmode
  have hnonneg : 0≤PiBinomial.pmf N p k := by
    unfold PiBinomial.pmf
    positivity
  have hA : 0<((k:ℝ)+1)*(1-p) := mul_pos (by positivity) (sub_pos.mpr hp1)
  have hh := mul_le_mul_of_nonneg_right (show ((k:ℝ)+1)*(1-p)≤((N:ℝ)-(k:ℝ))*p by linarith) hnonneg
  nlinarith only [he,hh,hA]

theorem pmf_le_boundary (N K : ℕ) (p : ℝ) (hp0 : 0≤p) (hp1 : p<1)
    (hKN : K≤N) (hmode : (K:ℝ)≤((N+1:ℕ):ℝ)*p) :
    ∀j≤K,PiBinomial.pmf N p j≤PiBinomial.pmf N p K := by
  intro j hj
  have hstep : ∀k<K,PiBinomial.pmf N p k≤PiBinomial.pmf N p (k+1) := by
    intro k hk
    apply pmf_le_next N k p hp0 hp1 (hk.trans_le hKN)
    exact (Nat.cast_le.mpr (Nat.succ_le_of_lt hk)).trans hmode
  have hchain : ∀k≤K,∀j≤k,PiBinomial.pmf N p j≤PiBinomial.pmf N p k := by
    intro k
    induction k with
    | zero=>
      intro _ j hj
      have he : j=0 := by omega
      exact he ▸ le_rfl
    | succ k ih=>
      intro hk j hj
      by_cases he : j=k+1
      · subst j; rfl
      · exact (ih (by omega) j (by omega)).trans (hstep k (by omega))
  exact hchain K le_rfl j hj

theorem binomial_tail_le_boundary (N K : ℕ) (p : ℝ) (hp0 : 0≤p) (hp1 : p<1)
    (hKN : K≤N) (hmode : (K:ℝ)≤((N+1:ℕ):ℝ)*p) :
    (IndependentCounts.binomial N p hp0 hp1.le).prob (fun r=>r.val≤K)≤
      ((N+1:ℕ):ℝ)*PiBinomial.pmf N p K := by
  rw [FiniteLaw.prob_eq_expect]
  unfold FiniteLaw.expect
  calc
    (∑r : Fin (N+1),(IndependentCounts.binomial N p hp0 hp1.le).mass r*
        (if r.val≤K then (1:ℝ) else 0))≤∑_r : Fin (N+1),PiBinomial.pmf N p K := by
      apply Finset.sum_le_sum
      intro r _
      rw [PiBinomial.binomial_mass]
      by_cases hr : r.val≤K
      · simp only [if_pos hr,mul_one]
        exact pmf_le_boundary N K p hp0 hp1 hKN hmode r.val hr
      · simp only [if_neg hr,mul_zero]
        unfold PiBinomial.pmf
        positivity
    _ = ((N+1:ℕ):ℝ)*PiBinomial.pmf N p K := by simp
lemma pmf_next_le (N k : ℕ) (p : ℝ) (hp0 : 0≤p) (hp1 : p<1)
    (hk : k<N) (hmode : ((N+1:ℕ):ℝ)*p≤((k+1:ℕ):ℝ)) :
    PiBinomial.pmf N p (k+1)≤PiBinomial.pmf N p k := by
  have he := pmf_adjacent N k p hk
  have hNp : ((N-k:ℕ):ℝ)=(N:ℝ)-(k:ℝ) := Nat.cast_sub hk.le
  have hkR : ((k+1:ℕ):ℝ)=(k:ℝ)+1 := Nat.cast_add_one k
  have hNR : ((N+1:ℕ):ℝ)=(N:ℝ)+1 := Nat.cast_add_one N
  rw [hNp,hkR] at he
  rw [hkR,hNR] at hmode
  have hnonneg : 0≤PiBinomial.pmf N p k := by unfold PiBinomial.pmf; positivity
  have hA : 0<((k:ℝ)+1)*(1-p) := mul_pos (by positivity) (sub_pos.mpr hp1)
  have hh := mul_le_mul_of_nonneg_right
    (show ((N:ℝ)-(k:ℝ))*p≤((k:ℝ)+1)*(1-p) by linarith) hnonneg
  nlinarith only [he,hh,hA]

theorem pmf_fraction_max (N K : ℕ) (hK0 : 0<K) (hKN : K<N) :
    ∀j≤N,PiBinomial.pmf N ((K:ℝ)/N) j≤PiBinomial.pmf N ((K:ℝ)/N) K := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (hK0.trans hKN)
  have hK : (0:ℝ)<K := Nat.cast_pos.mpr hK0
  let q : ℝ := (K:ℝ)/N
  have hq0 : 0<q := div_pos hK hN
  have hq1 : q<1 := (div_lt_one hN).2 (Nat.cast_lt.mpr hKN)
  have hNq : (N:ℝ)*q=K := by dsimp [q]; field_simp
  have hN1 : ((N+1:ℕ):ℝ)*q=(K:ℝ)+q := by push_cast; nlinarith only [hNq]
  intro j hj
  by_cases hjK : j≤K
  · apply pmf_le_boundary N K q hq0.le hq1 hKN.le _ j hjK
    rw [hN1]
    linarith
  · have hchain : ∀j,K≤j→j≤N→PiBinomial.pmf N q j≤PiBinomial.pmf N q K := by
      intro j
      induction j with
      | zero=>intro hk; omega
      | succ j ih=>
        intro hKj hjN
        by_cases he : j+1=K
        · rw [he]
        · have hKj' : K≤j := by omega
          have hm : ((N+1:ℕ):ℝ)*q≤((j+1:ℕ):ℝ) := by
            rw [hN1]
            have hh : (K:ℝ)≤j := Nat.cast_le.mpr hKj'
            push_cast
            linarith
          exact (pmf_next_le N j q hq0.le hq1 (by omega) hm).trans (ih hKj' (by omega))
    exact hchain j (by omega) hj

theorem pmf_fraction_lower (N K : ℕ) (hK0 : 0<K) (hKN : K<N) :
    1/((N+1:ℕ):ℝ)≤PiBinomial.pmf N ((K:ℝ)/N) K := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (hK0.trans hKN)
  have hq0 : 0≤(K:ℝ)/N := div_nonneg (Nat.cast_nonneg _) hN.le
  have hq1 : (K:ℝ)/N≤1 := ((div_lt_one hN).2 (Nat.cast_lt.mpr hKN)).le
  have hs := (IndependentCounts.binomial N ((K:ℝ)/N) hq0 hq1).total
  simp_rw [PiBinomial.binomial_mass] at hs
  have hsum : (∑j : Fin (N+1),PiBinomial.pmf N ((K:ℝ)/N) j.val)≤
      ((N+1:ℕ):ℝ)*PiBinomial.pmf N ((K:ℝ)/N) K := by
    calc
      (∑j : Fin (N+1),PiBinomial.pmf N ((K:ℝ)/N) j.val)≤
          ∑_j : Fin (N+1),PiBinomial.pmf N ((K:ℝ)/N) K :=
        Finset.sum_le_sum (fun j _=>pmf_fraction_max N K hK0 hKN j.val (by omega))
      _ = _ := by simp
  rw [hs] at hsum
  apply (div_le_iff₀ (by positivity : (0:ℝ)<((N+1:ℕ):ℝ))).2
  nlinarith only [hsum]

lemma pmf_pos (N K : ℕ) (p : ℝ) (hp0 : 0<p) (hp1 : p<1) (hKN : K≤N) :
    0<PiBinomial.pmf N p K := by
  unfold PiBinomial.pmf
  exact mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hKN)) (pow_pos hp0 _))
    (pow_pos (sub_pos.mpr hp1) _)

theorem log_pmf_change_parameter (N K : ℕ) (p : ℝ) (hK0 : 0<K) (hKN : K<N)
    (hp0 : 0<p) (hp1 : p<1) :
    log (PiBinomial.pmf N p K)=log (PiBinomial.pmf N ((K:ℝ)/N) K)-
      (N:ℝ)*Ample.binaryKL ((K:ℝ)/N) p := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (hK0.trans hKN)
  have hK : (0:ℝ)<K := Nat.cast_pos.mpr hK0
  have hq : 0<(K:ℝ)/N := div_pos hK hN
  have hq1 : (K:ℝ)/N<1 := (div_lt_one hN).2 (Nat.cast_lt.mpr hKN)
  have hch : (N.choose K:ℝ)≠0 := (Nat.cast_pos.mpr (Nat.choose_pos hKN.le)).ne'
  have hsub : ((N-K:ℕ):ℝ)=(N:ℝ)-(K:ℝ) := Nat.cast_sub hKN.le
  unfold PiBinomial.pmf Ample.binaryKL
  rw [Real.log_mul (mul_ne_zero hch (pow_ne_zero _ hp0.ne')) (pow_ne_zero _ (sub_pos.mpr hp1).ne'),
    Real.log_mul hch (pow_ne_zero _ hp0.ne'),
    Real.log_mul (mul_ne_zero hch (pow_ne_zero _ hq.ne')) (pow_ne_zero _ (sub_pos.mpr hq1).ne'),
    Real.log_mul hch (pow_ne_zero _ hq.ne')]
  simp only [Real.log_pow]
  rw [Real.log_div hq.ne' hp0.ne',Real.log_div (sub_pos.mpr hq1).ne' (sub_pos.mpr hp1).ne',hsub]
  field_simp
  ring

theorem log_pmf_entropy_lower (N K : ℕ) (p : ℝ) (hK0 : 0<K) (hKN : K<N)
    (hp0 : 0<p) (hp1 : p<1) :
    -log ((N+1:ℕ):ℝ)-(N:ℝ)*Ample.binaryKL ((K:ℝ)/N) p≤
      log (PiBinomial.pmf N p K) := by
  have hmode := pmf_fraction_lower N K hK0 hKN
  have hl := Real.log_le_log (by positivity : (0:ℝ)<1/((N+1:ℕ):ℝ)) hmode
  rw [Real.log_div one_ne_zero (by positivity),Real.log_one,zero_sub] at hl
  rw [log_pmf_change_parameter N K p hK0 hKN hp0 hp1]
  linarith

lemma pmf_le_lower_tail (N K : ℕ) (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (hKN : K≤N) :
    PiBinomial.pmf N p K≤
      (IndependentCounts.binomial N p hp0 hp1).prob (fun r=>r.val≤K) := by
  classical
  let μ:=IndependentCounts.binomial N p hp0 hp1
  let k : Fin (N+1):=⟨K,by omega⟩
  have hm := μ.prob_mono (E:=fun r=>r=k) (F:=fun r=>r.val≤K) (by
    intro r hr
    subst r
    exact le_rfl)
  simpa only [FiniteLaw.prob_eq_expect,FiniteLaw.expect_singleton,μ,k,PiBinomial.binomial_mass] using hm

lemma continuousAt_binaryKL_left (p ρ : ℝ) (hp0 : 0<p) (hp1 : p<1)
    (hρ0 : 0<ρ) (hρ1 : ρ<1) : ContinuousAt (fun x=>Ample.binaryKL x p) ρ := by
  unfold Ample.binaryKL
  exact (continuousAt_id.mul ((continuousAt_id.div_const p).log (div_pos hρ0 hp0).ne')).add
    ((continuousAt_const.sub continuousAt_id).mul
      (((continuousAt_const.sub continuousAt_id).div_const (1-p)).log
        (div_pos (sub_pos.mpr hρ1) (sub_pos.mpr hp1)).ne'))

theorem eventually_pmf_exponential_lower (N K : ℕ→ℕ) (p ρ : ℝ)
    (hp0 : 0<p) (hp1 : p<1) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    (hN : Tendsto N atTop atTop)
    (hNm : Tendsto (fun m=>(N m:ℝ)/(m:ℝ)) atTop (𝓝 1))
    (hKN : Tendsto (fun m=>(K m:ℝ)/(N m:ℝ)) atTop (𝓝 ρ))
    (r : ℝ) (hr : Ample.binaryKL ρ p<r) :
    ∀ᶠ m : ℕ in atTop, exp (-(m:ℝ)*r)≤PiBinomial.pmf (N m) p (K m) := by
  have hN0 : ∀ᶠ m in atTop,0<N m := hN.eventually_gt_atTop 0
  have hK0:=hKN.eventually_const_lt hρ0
  have hK1:=hKN.eventually_lt_const hρ1
  have hlog : Tendsto (fun m=>log ((N m+1:ℕ):ℝ)/(N m:ℝ)) atTop (𝓝 0) := by
    have hadd : Tendsto (fun m : ℕ=>(N m:ℝ)+1) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp hN).atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
    have he := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hadd
    convert he using 1
    simp [Function.comp_def]
  have hlogm : Tendsto (fun m=>log ((N m+1:ℕ):ℝ)/(m:ℝ)) atTop (𝓝 0) := by
    have he:=hlog.mul hNm
    have hfun : (fun m=>log ((N m+1:ℕ):ℝ)/(N m:ℝ)*((N m:ℝ)/(m:ℝ)))=ᶠ[atTop]
        (fun m=>log ((N m+1:ℕ):ℝ)/(m:ℝ)) := by
      filter_upwards [hN0] with m hm
      have hmR : (N m:ℝ)≠0 := (Nat.cast_pos.mpr hm).ne'
      field_simp
    simpa only [zero_mul] using he.congr' hfun
  have hKL := (continuousAt_binaryKL_left p ρ hp0 hp1 hρ0 hρ1).tendsto.comp hKN
  have hbound := (hlogm.add (hNm.mul hKL)).eventually_lt_const (by simpa using hr)
  filter_upwards [hN0,hK0,hK1,hbound,eventually_gt_atTop (0:ℕ)] with m hNpos hKpos hKsmall hb hm
  have hNR : (0:ℝ)<N m := Nat.cast_pos.mpr hNpos
  have hKR : (0:ℝ)<K m := (div_pos_iff_of_pos_right hNR).mp hKpos
  have hKnat : 0<K m := Nat.cast_pos.mp hKR
  have hKlt : K m<N m := Nat.cast_lt.mp ((div_lt_one hNR).mp hKsmall)
  have hpmf := pmf_pos (N m) (K m) p hp0 hp1 hKlt.le
  have hlo := log_pmf_entropy_lower (N m) (K m) p hKnat hKlt hp0 hp1
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hbb : log ((N m+1:ℕ):ℝ)+(N m:ℝ)*Ample.binaryKL ((K m:ℝ)/N m) p<(m:ℝ)*r := by
    simp only [Function.comp_apply] at hb
    have hbid : log ((N m+1:ℕ):ℝ)/(m:ℝ)+(N m:ℝ)/(m:ℝ)*
        Ample.binaryKL ((K m:ℝ)/N m) p=
        (log ((N m+1:ℕ):ℝ)+(N m:ℝ)*Ample.binaryKL ((K m:ℝ)/N m) p)/(m:ℝ) := by ring
    rw [hbid] at hb
    simpa only [mul_comm r] using (div_lt_iff₀ hmR).mp hb
  apply (Real.le_log_iff_exp_le hpmf).mp
  linarith

end FCAppendix.Affine.LowBody
