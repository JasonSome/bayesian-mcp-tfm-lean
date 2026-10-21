import FCAppendix.Affine.Uniform06.PhysicalRootTransfer
import FCAppendix.Affine.Uniform06.EarlyCoarseMargins
import FCAppendix.Affine.Uniform06.EqualOnlyCountTransfer

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceLowPhysicalRootTransfer

open MeasureTheory Set Filter LowBody
open scoped Topology BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open MixedIntervalLLT PhysicalSourceMoments RawMomentPartition ClampedMomentBounds
open LiteralMomentBounds LiteralBadCountTransfer SamplingPopulation EarlyCoarseMargins

theorem original_summed_response_replacement (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 (FullJointLaw.law i)))
    (A : CenteredArray RowRival) [∀ n,Nonempty (Fin (A.N n))] (hgap : A.CompactGap)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : ∀ n,A.N n=m n-1)
    (b θ r : ℕ → ℝ) (g : ℕ → GuardData)
    (cm : ∀ n,(Fin (A.N n) → Fin 4) → ℝ)
    (hlaw : ∀ n,A.law n=tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))
    (hY : ∀ n,A.Y n=integerSign)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=demand (xi i) (b n) x-r n)
    {hi Θ t0 b0 θ0 : ℝ} (hhi : hi< entry i) (ht0 : 0< t0)
    (hb : ∀ n,b n ∈ Icc (cutoff i/2) hi)
    (hθ : ∀ n,t0≤θ n ∧ θ n≤Θ)
    (hblim : Tendsto b atTop (𝓝 b0)) (hθlim : Tendsto θ atTop (𝓝 θ0))
    (hvalue : ∀ n,(G n:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),
      p ∈ EarlyJointCompactness.box (cutoff i) (ReceiptGap.cap i))
    (hactive : ∀ᶠ n in atTop,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),
      p.1 ∈ Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1|≤ cutoff i/10000)
    (hmatch : ∀ᶠ n in atTop,(∫ x,demand (xi i) (b n) x
      ∂tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))=
        (capacity (m n):ℝ)/(A.N n:ℝ))
    (hLlim : Tendsto (fun n => (g n).multiplier) atTop (𝓝 (entry i)))
    (hR : ∀ n,(g n).radius≤ cutoff i/100)
    (hg : ∀ n,0<(g n).margin ∧ 0<(g n).population ∧ 0<(g n).requiredDemand)
    (hreq : ∀ n,(g n).requiredDemand=PrefixRoot.requiredDemand i)
    (hbL : ∀ n,b n≤(g n).multiplier)
    (hgl : ∀ n,0<(g n).multiplier-(g n).radius)
    (hbl : ∀ n,b n≤(g n).multiplier-(g n).radius)
    (q : Fin 2) :
    Tendsto (fun n => (A.N n:ℝ)^(q.val+2)*tiltedPhysical i (G n:Measure (ℝ × ℝ))
        (A.N n) (capacity (m n)) (g n) (cm n) (b n) (θ n) (q.val+1)-
      (1/(b0*FullReciprocalMean.nu i b0 θ0))^(q.val+1)*(A.N n:ℝ)*
        ∫ ω : Fin (A.N n) → RowRival,
          literalMoment i (capacity (m n)) (g n) (cm n) (b n) (θ n) (q.val+1) ω
            ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)) atTop (𝓝 0) := by
  let U := ReceiptGap.cap i
  let lo := floorPrice i
  let ν := FullReciprocalMean.nu i b0 θ0
  let c := fun n => capacity (m n)
  have hU : 0< U := (ReceiptGap.cap_bounds i).1
  have hlo : 0< lo := (floorPrice_bounds i).1
  have hlow : lo< cutoff i/2 := (floorPrice_bounds i).2
  have hbp (n : ℕ) : 0< b n := (half_pos (cutoff_pos i)).trans_le (hb n).1
  have hbiU : hi≤ U := hhi.le.trans (ReceiptGap.entry_below_cap i).le
  have hbU (n : ℕ) : b n≤ U := (hb n).2.trans hbiU
  have hb0 := isClosed_Icc.mem_of_tendsto hblim (Eventually.of_forall hb)
  have hb0p : 0< b0 := (half_pos (cutoff_pos i)).trans_le hb0.1
  have hb0L : b0< entry i := hb0.2.trans_lt hhi
  have hν : 0<ν := FullReciprocalMean.nu_pos i hb0p hb0L θ0
  have hΘ : 0<Θ := ht0.trans_le ((hθ 0).1.trans (hθ 0).2)
  have hcapG (n : ℕ) : ∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2≤ U :=
    (hbox n).mono fun _ hp => hp.2.2
  have hm2 (n : ℕ) : 2≤ m n := by
    have hn := Nat.cast_pos.mp (A.N_pos n)
    rw [hN] at hn
    omega
  have hcapN (n : ℕ) : (c n:ℝ)≤ A.N n := by
    rw [hN]
    have hc : capacity (m n)≤ m n-1 := by
      unfold capacity
      omega
    exact_mod_cast hc
  have hfloor (n : ℕ) : |(c n:ℝ)-(A.N n:ℝ)*rho|≤1 := by
    rw [hN]
    exact SourceCoarseIntegral.capacity_centered_error (hm2 n)
  obtain ⟨unusedLo,ε0,Q,a,d,hunused,hε0,hQ,ha,hd,hfin⟩ := eventual_source_margins i G m b θ g
    hm hhi hΘ hb hvalue (Eventually.of_forall hcapG) hactive
    (Eventually.of_forall fun n => ⟨ht0.trans_le (hθ n).1,(hθ n).2⟩)
    (by simpa only [← hN] using hmatch) hLlim (Eventually.of_forall hR) (Eventually.of_forall hg)
  let g0 : GuardData := {g 0 with multiplier:=entry i}
  let z := weightMean i (FullJointLaw.law i:Measure (ℝ × ℝ)) b0 θ0 g0
  have hz : 0< z := (full_sampling_means_positive i hb0p θ0 g0 rfl (hreq 0)).1
  have hwlim := (actual_one_user_means_tendsto i G (FullJointLaw.law i) hG b θ g g0
    hbp hb0p (fun n => (hbp n).trans_le (hbL n)) (EarlyMean.entry_pos i)
    (hg 0).2.2 (fun n => (hreq n).trans (hreq 0).symm) hblim hθlim hLlim).1
  let ε := min ε0 (z/16)
  let γ := min (ν/2) (Q/(4*U))
  have hε : 0<ε := lt_min hε0 (by positivity)
  have hγ : 0<γ := lt_min (by positivity) (by positivity)
  have hγν : γ≤ν := (min_le_left _ _).trans (by linarith)
  have hγQ : γ≤ Q/(4*U) := min_le_right _ _
  have hεold : ε≤ε0 := min_le_left _ _
  have hεz : 8*ε≤ z := by have hh := min_le_right ε0 (z/16); linarith
  have hfields : ∀ᶠ n in atTop,
      countMargins i (G n:Measure (ℝ × ℝ)) (A.N n) (c n) (b n) (θ n) ε ∧
      Q≤(TiltedGood.law i (G n:Measure (ℝ × ℝ)) (b n) (θ n)).real
        (CostAmplification.activeStrip (entry i) U) ∧ 12*ε≤ Q := by
    filter_upwards [hfin] with n hn
    rcases hn with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hp,hrm,hs,hεQ,_,_,_,_⟩
    have hNr := (A.N_pos n).le
    have hεN := mul_le_mul_of_nonneg_right hεold hNr
    rw [← hN] at hp hrm
    refine ⟨⟨hfloor n,by linarith,by linarith⟩,hs,by linarith⟩
  have hcmatch : ∀ᶠ n in atTop,(c n:ℝ)=(A.N n:ℝ)*r n := by
    filter_upwards [hmatch] with n hn
    have hDi : Integrable (demand (xi i) (b n)) (A.law n) :=
      Integrable.of_mem_Icc 0 1 (measurable_demand _ _).aemeasurable
        (ae_of_all _ (demand_bounds (xi_pos i) (hbp n)))
    have hm' := integral_congr_ae (hcenter n)
    rw [A.mean_X,integral_sub hDi (integrable_const (r n)),integral_const] at hm'
    simp only [probReal_univ,one_smul] at hm'
    rw [← hlaw] at hn
    have heq : r n=(c n:ℝ)/(A.N n:ℝ) := by dsimp only [c]; linarith
    have hh := (eq_div_iff (A.N_pos n).ne').mp heq
    nlinarith
  have hθ0 : 0<θ0 := ht0.trans_le
    (isClosed_Icc.mem_of_tendsto hθlim (Eventually.of_forall hθ)).1
  let τ : Fin 2 → ℕ → ℝ := fun j n => if j=0 then θ n else θ n/2
  let τ0 : Fin 2 → ℝ := fun j => if j=0 then θ0 else θ0/2
  have hτ (j : Fin 2) (n : ℕ) : t0/2≤τ j n ∧ τ j n≤Θ := by
    dsimp only [τ]
    split_ifs <;> constructor <;> linarith [(hθ n).1,(hθ n).2]
  have hτlim (j : Fin 2) : Tendsto (τ j) atTop (𝓝 (τ0 j)) := by
    dsimp only [τ,τ0]
    split_ifs
    · exact hθlim
    · exact hθlim.div_const 2
  have hτ0 (j : Fin 2) : 0<τ0 j := by dsimp [τ0]; split_ifs <;> positivity
  have hmoment (j : Fin 2) := EqualOnlyCountTransfer.original_low_literal_moments_test i G A hgap
    b θ (τ j) r c g cm hlaw hY hcenter hcmatch hbp hbL hgl hbl hcapN hg
    (half_pos ht0) (hτ j) (hτlim j) (hτ0 j) hε (entry i) U (hfields.mono fun _ hn => hn.1)
  obtain ⟨B0,hB0,hB0e⟩ := finite_family_bounded_above
    (fun j : Fin 2 × Fin 3 => fun n => (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
      literalMoment i (c n) (g n) (cm n) (b n) (τ j.1 n) j.2.val ω
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))
    (fun j : Fin 2 × Fin 3 => MixedIntervalLLT.density A.vX A.vY*(j.2.val.factorial:ℝ)/
      (τ0 j.1)^(j.2.val+1)) (fun j => hmoment j.1 j.2)
  have hkerr := EqualOnlyCountTransfer.original_low_count_replacement i G A.N c A.market
    (fun n => Nat.cast_pos.mp (A.N_pos n)) b θ θ g cm hbp hbL hgl hbl
    (fun n => ht0.le.trans (hθ n).1) hcapN hg hε (entry i) U
    (hfields.mono fun _ hn => hn.1) 0 1
  have hklim : Tendsto (fun n => (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
      ((imbalanceSum ω).natAbs:ℝ)*literalMoment i (c n) (g n) (cm n) (b n) (θ n) 0 ω
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)) atTop (𝓝 0) := by
    apply hkerr.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    rw [← hlaw n]
    apply congrArg ((A.N n:ℝ)*·)
    apply integral_congr_ae
    apply ae_of_all
    intro ω
    simp only [pow_one]
    by_cases hy : imbalanceSum ω=0
    · simp only [hy,Int.natAbs_zero,Nat.cast_zero,zero_mul]
    · have hz : EqualOnlyRareMoments.emptyMoment i (c n) (b n) (θ n) 0 ω=0 := by
        simp only [EqualOnlyRareMoments.emptyMoment,if_neg hy]
      rw [hz,sub_zero,abs_of_nonneg
        (EqualOnlyRareMoments.low_literal_polynomial i (c n) (g n) (cm n)
          (hbp n) (hbL n) (hgl n) (hbl n) (hg n).1 (hg n).2.1 (hg n).2.2
          (ht0.le.trans (hθ n).1) (hcapN n) 0 ω).1]
  let B := B0+2
  have hB : 0< B := by dsimp [B]; linarith
  let E := fun n => LiteralRootGood.good i (G n:Measure (ℝ × ℝ)) (g n)
    (entry i) U (b n) (θ n) (A.N n) ε
  have hbad : ∀ᶠ n in atTop,(Measure.pi (fun _ : Fin (A.N n) =>
      tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))).real (E n)ᶜ≤
        10*Real.exp (-(2*ε^2)*(A.N n:ℝ)) := Eventually.of_forall fun n =>
    LiteralRootGood.good_complement i (G n:Measure (ℝ × ℝ)) (g n) (entry i) U
      (hbp n) (θ n) (A.N n) (Nat.cast_pos.mp (A.N_pos n)) hε.le
  have hmom : ∀ᶠ n in atTop,
      (∀ q : Fin 3,(A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
        literalMoment i (c n) (g n) (cm n) (b n) (θ n) q.val ω
          ∂Measure.pi (fun _ : Fin (A.N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))≤ B ∧
        (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
          literalMoment i (c n) (g n) (cm n) (b n) (θ n/2) q.val ω
            ∂Measure.pi (fun _ : Fin (A.N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))≤ B) ∧
      (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
        ((imbalanceSum ω).natAbs:ℝ)*literalMoment i (c n) (g n) (cm n) (b n) (θ n) 0 ω
          ∂Measure.pi (fun _ : Fin (A.N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))≤ B := by
    filter_upwards [hB0e,hklim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn hkn
    simp only [hlaw] at hn hkn
    refine ⟨fun q => ⟨?_,?_⟩,hkn.le.trans (by dsimp [B]; linarith)⟩
    · apply le_trans (b := B0) ?_ (by dsimp [B]; linarith)
      simpa only [τ,if_pos rfl] using hn (0,q)
    · apply le_trans (b := B0) ?_ (by dsimp [B]; linarith)
      simpa only [τ,show (1:Fin 2)≠0 by decide,if_false] using hn (1,q)
  have hpoly (n : ℕ) : ∀ᵐ ω ∂Measure.pi (fun _ : Fin (A.N n) =>
      tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)),
      (∀ q : Fin 3,literalMoment i (c n) (g n) (cm n) (b n) (θ n) q.val ω
          ∈ Icc (0:ℝ) ((A.N n:ℝ)^q.val) ∧
        literalMoment i (c n) (g n) (cm n) (b n) (θ n/2) q.val ω
          ∈ Icc (0:ℝ) ((A.N n:ℝ)^q.val)) ∧
      ∀ q : Fin 2,physicalMoment i (c n) (g n) (cm n) (b n) (θ n) (q.val+1) ω
        ∈ Icc (0:ℝ) 1 := by
    apply ae_of_all
    intro ω
    have hh (d : ℕ) (τ : ℝ) (hτ : 0≤τ) := EqualOnlyRareMoments.low_literal_polynomial i
      (c n) (g n) (cm n) (hbp n) (hbL n) (hgl n) (hbl n) (hg n).1 (hg n).2.1
      (hg n).2.2 hτ (hcapN n) d ω
    refine ⟨fun q => ⟨hh _ _ (ht0.le.trans (hθ n).1),hh _ _ (by linarith [(hθ n).1])⟩,?_⟩
    intro q
    exact EqualOnlyRareMoments.low_physical_bounded i (c n) (g n) (cm n) (hbp n)
      (hbL n) (hgl n) (hbl n) (hg n).1 (hg n).2.1 (hg n).2.2
      (ht0.le.trans (hθ n).1) (hcapN n) (q.val+1) (by omega) ω
  have hloU : U/2≤ lo := by
    have hξ : xi i≤1/2 := by cases i <;> norm_num [xi,xiQ,etaQ]
    dsimp [lo,floorPrice]
    nlinarith
  have hrows : ∀ᶠ n in atTop,∀ᵐ ω ∂Measure.pi (fun _ : Fin (A.N n) =>
      tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)),ω ∈ E n →
      (∀ q : Fin 2,physicalMoment i (c n) (g n) (cm n) (b n) (θ n) (q.val+1) ω=0 ∧
        literalMoment i (c n) (g n) (cm n) (b n) (θ n) (q.val+1) ω=0) ∨
      (RawPathAdapter.ValidCounts (c n) ω ∧ (∀ j,(ω j).1=0 → (ω j).2≤ U) ∧
      (imbalanceSum ω=0 ∨ ∀ j,0≤ rawH (xi i) (b n) (ω j)) ∧
      ((imbalanceSum ω).natAbs:ℝ)< FCAppendix.Affine.WeightedSampling.totalWeight
        (FiniteSampledLaplace.rowWeights (rawWeight (xi i) (g n)) (rawWeight_bounds (xi i) (g n)) ω) ∧
      γ+((imbalanceSum ω).natAbs:ℝ)/(lo*(A.N n:ℝ))≤
        RareEmpiricalReplacement.empirical (FullReciprocalMean.reciprocal (b n)) (A.N n) ω) := by
    filter_upwards [hfields,hwlim.eventually (Ioi_mem_nhds (show z/2< z by linarith))] with n hn hwm
    have hrawcap : ∀ᵐ x ∂tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n),
        x.1=0 → x.2≤ U := (tilted_absolutelyContinuous _ _).ae_le
      (SourceCoarseIntegral.original_retained_bid_cap i (G n:Measure (ℝ × ℝ)) (hcapG n))
    have hrawno := TiltedGood.tilted_no_active_tag i (G n:Measure (ℝ × ℝ)) (b n) (θ n)
    letI := tiltedSource_probability i (G n:Measure (ℝ × ℝ)) (hbp n) (θ n)
    have hcoord (j : Fin (A.N n)) := (measurePreserving_eval (fun _ : Fin (A.N n) =>
      tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)) j).quasiMeasurePreserving.ae
        (hrawcap.and hrawno)
    filter_upwards [ae_all_iff.mpr hcoord] with ω hω hEω
    have hh := LiteralRootGood.original_good_path_conditions i (G n:Measure (ℝ × ℝ)) (g n)
      (hbp n) ((hb n).2.trans_lt hhi) hU hlo hloU (Nat.cast_pos.mp (A.N_pos n))
      hn.1.1 hn.1.2.1 hn.1.2.2 hQ hn.2.2 hn.2.1 hz hεz hwm.le ω
      (fun j => (hω j).2) hEω
    by_cases hy : imbalanceSum ω=0
    · exact Or.inr ⟨hh.1,fun j => (hω j).1,Or.inl hy,hh.2.1,
        (add_le_add hγQ le_rfl).trans hh.2.2⟩
    · apply Or.inl
      have hne : (patternTemplate (c n) (fun j => (ω j).1)).residual₀≠
          (patternTemplate (c n) (fun j => (ω j).1)).residual₁ :=
        fun he => hy ((imbalance_zero_iff_equal (c n) ω hh.1).mpr he)
      have hz (d : ℕ) := EqualOnlyRareMoments.unequal_literal_zero i (c n) (g n) (cm n)
        (hbp n) (hbL n) (hgl n) (hbl n) (hg n).1 (hg n).2.1 (hg n).2.2 (θ n) d ω hne
      intro q
      have hp := physicalMoment_le_strict_zero i (c n) (g n) (cm n) (hbp n) (θ n)
        (q.val+1) (by omega) ω
      rw [hz 0] at hp
      exact ⟨le_antisymm hp.2 hp.1,hz (q.val+1)⟩
  have ht := PhysicalRootTransfer.constructed_response_replacement i G hG A.N c A.market
    (fun n => Nat.cast_pos.mp (A.N_pos n)) b θ g cm E
    (fun n => LiteralRootGood.measurable_good i _ _ _ _ _ _ _ _) hlo hlow hU hb hbiU
    hbL (fun n => (hg n).2.2) le_rfl hbox ht0 hθ hblim hθlim hb0L hγ hγν hε hB
    hpoly hmom hbad hrows q
  simpa only [← hlaw,c] using ht

end FCAppendix.Affine.Uniform06.SourceLowPhysicalRootTransfer
