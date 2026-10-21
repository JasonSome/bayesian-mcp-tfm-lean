import FCAppendix.Existence.SingletonEnvelope
import FCAppendix.Existence.SingletonLimits
import FCAppendix.Existence.SingletonRoutes

noncomputable section
namespace FCAppendix.Existence.Singleton
open MeasureTheory Set Filter Topology
open RankEnvelope

theorem source_bid_formula (mu : Measure ℝ) [IsFiniteMeasure mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    {w : ℝ} (hw : 0 ≤ w) : singletonBid mu r c n w =
      w-(∫ x in 0..w, rank mu (r+1) c n x)/rank mu (r+1) c n w := by
  rw [singletonBid_eq mu hc hcr hn hmass hw]
  simp only [bid,utility,sub_self,zero_mul,zero_add]

theorem source_contact_at_zero (mu : Measure ℝ) [IsFiniteMeasure mu]
    (n : ℕ) (hsupport : ∀ᵐ w ∂mu, 0<w) : contactTail mu n 0=mu.real univ/(n:ℝ) := by
  have he : mu.real (Ioi 0)=mu.real univ := by
    apply measureReal_congr
    filter_upwards [hsupport] with w hw
    exact propext ⟨fun _ => trivial,fun _ => hw⟩
  rw [contactTail,he]

theorem singleton_integral_success_tendsto (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    {n : ℕ} (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    (R C : ℕ → ℕ) (hR : Tendsto R atTop atTop) (hc : ∀ t, 1 ≤ C t)
    (hcr : ∀ t, C t ≤ R t+1) (hsupport : ∀ᵐ v ∂mu, 0<v)
    {rho : ℝ} (hDensity : Tendsto (fun t => (C t:ℝ)/((R t:ℝ)+2)) atTop (𝓝 rho))
    (hgap : mu.real univ/(n:ℝ)<rho) :
    Tendsto (fun t => ∫ v, rank mu (R t+1) (C t) n v ∂mu) atTop (𝓝 (mu.real univ)) := by
  have hN : Tendsto (fun t => R t+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hR
  have hDen : Tendsto (fun t => (C t:ℝ)/(((R t+1:ℕ):ℝ)+1)) atTop (𝓝 rho) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hDensity
  have hq0 := ample_rank_zero_tendsto_one mu hn hmass (fun t => R t+1) C hN
    (fun t => (hcr t).trans (Nat.le_succ _)) hDen
    (by rw [source_contact_at_zero mu n hsupport]; exact hgap)
  have hlo := hq0.const_mul (mu.real univ)
  rw [mul_one] at hlo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
  · intro t
    exact (integral_rank_bounds mu (R t) (C t) (hc t) (hcr t) hn hmass (hsupport.mono fun _ hv => hv.le)).1
  · intro t
    exact (integral_rank_bounds mu (R t) (C t) (hc t) (hcr t) hn hmass (hsupport.mono fun _ hv => hv.le)).2

theorem singleton_bids_tendsto_uniformly_zero (mu : Measure ℝ) [IsFiniteMeasure mu]
    {n : ℕ} (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    (R C : ℕ → ℕ) (hR : Tendsto R atTop atTop) (hc : ∀ t, 1 ≤ C t)
    (hcr : ∀ t, C t ≤ R t+1) (hsupport : ∀ᵐ v ∂mu, 0<v) (H : ℝ)
    {rho : ℝ} (hDensity : Tendsto (fun t => (C t:ℝ)/((R t:ℝ)+2)) atTop (𝓝 rho))
    (hgap : mu.real univ/(n:ℝ)<rho) :
    TendstoUniformlyOn (fun t w => singletonBid mu (R t) (C t) n w) (fun _ => 0) atTop (Icc 0 H) := by
  have hN : Tendsto (fun t => R t+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hR
  have hDen : Tendsto (fun t => (C t:ℝ)/(((R t+1:ℕ):ℝ)+1)) atTop (𝓝 rho) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hDensity
  have hq0 := ample_rank_zero_tendsto_one mu hn hmass (fun t => R t+1) C hN
    (fun t => (hcr t).trans (Nat.le_succ _)) hDen
    (by rw [source_contact_at_zero mu n hsupport]; exact hgap)
  have he := uniform_bid_bound_tendsto_zero hq0 H
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  filter_upwards [he.eventually (eventually_lt_nhds heps)] with t ht w hw
  have hb := zero_bid_uniform_bound (rank_monotone mu (hc t) (hcr t) hn hmass)
    (rank_pos mu _ _ (hc t) hn hmass) (fun v => (rank_bounds mu _ _ hn hmass v).2) hw.1 hw.2
  rw [singletonBid_eq mu (hc t) (hcr t) hn hmass hw.1]
  simpa only [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg hb.1] using hb.2.trans_lt ht

theorem exists_singleton_all_routes_threshold (mu : Measure ℝ) [IsFiniteMeasure mu]
    {n : ℕ} (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    (R C : ℕ → ℕ) (hR : Tendsto R atTop atTop) (hc : ∀ t, 1 ≤ C t)
    (hcr : ∀ t, C t ≤ R t+1) (hsupport : ∀ᵐ v ∂mu, 0<v)
    {rho : ℝ} (hDensity : Tendsto (fun t => (C t:ℝ)/((R t:ℝ)+2)) atTop (𝓝 rho))
    (hgap : mu.real univ/(n:ℝ)<rho) (A G : Schedule n)
    (g d H : ℝ) (hg : 0 ≤ g) (hd0 : 0<d) (hG1 : G.charge 1=1)
    (hd : ∀ r : ℕ, 2 ≤ r → r ≤ n → d ≤ g*(G.charge r-1)) :
    ∃ T : ℕ, ∀ t, T ≤ t → ∀ w ∈ Icc (0:ℝ) H, ∀ b : ℝ, 0 ≤ b →
    ∀ law : CountLaw n, 2*rank mu (R t+1) (C t) n 0-1 ≤ law.prob (fun r => 2 ≤ r.val) →
      law.utility (g+w) b g A G < utility (rank mu (R t+1) (C t) n) 0 0 w := by
  have hN : Tendsto (fun t => R t+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hR
  have hDen : Tendsto (fun t => (C t:ℝ)/(((R t+1:ℕ):ℝ)+1)) atTop (𝓝 rho) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hDensity
  have hq0 := ample_rank_zero_tendsto_one mu hn hmass (fun t => R t+1) C hN
    (fun t => (hcr t).trans (Nat.le_succ _)) hDen
    (by rw [source_contact_at_zero mu n hsupport]; exact hgap)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_costly_duplicate_gap (H:=H) hq0 hd0)
  refine ⟨T,?_⟩
  intro t ht w hw b hb law hpair
  apply all_duplicate_routes_strictly_worse law A G hb hg (by simpa only [add_sub_cancel_left] using hw.1)
    (by simpa only [add_sub_cancel_left] using hw.2) hd0 (rank_bounds mu _ _ hn hmass 0).2 hG1 hd
    hpair (hT t ht)
  simpa only [add_sub_cancel_left] using zero_utility_lower (rank_monotone mu (hc t) (hcr t) hn hmass) hw.1

end FCAppendix.Existence.Singleton
