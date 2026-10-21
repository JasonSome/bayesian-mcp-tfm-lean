import FCAppendix.Affine.Uniform06.EntryModerateReciprocal

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace FCAppendix.Affine.Uniform06.EntryLiteralModerate
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.ExponentialTilt
open EntryEarlySourceLimits EntryRawSignMoments EntryUntilting EntryRawTiltedFiber
open EntryRawModerate EntryOriginalModerate EntryGoodModerate EntryRelativeWeight
open EntryLiteralResponseGeometry EntryLiteralResponseMoments EntryLiteralCanonicalTransfer
open EntryModerateRootFinite EntryResponseTransfer EntryReciprocalLimit
open scoped BigOperators

variable {N C : ℕ}

lemma response_bounds (ν : Measure RowRival) (i : Row) (g : LiteralExperiment.GuardData)
    (b A U ε : ℝ) (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    response ν i C g b A U ε x∈Icc (0:ℝ) 1 := by
  unfold response
  split_ifs
  · exact complement_bounds i C g b x
  · norm_num

lemma responseMoment_bounds (ν : Measure RowRival) (i : Row) (g : LiteralExperiment.GuardData)
    (b A U ε : ℝ) (k : ℕ) (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    deficitMoment k (response ν i C g b A U ε x)∈Icc (0:ℝ) 1 := by
  refine ⟨deficitMoment_nonneg _ _,?_⟩
  have hp := response_bounds ν i g b A U ε x (C := C)
  by_cases hk : k=0
  · simp only [hk,deficitMoment_zero]
    split_ifs <;> norm_num
  · simp only [deficitMoment,if_neg hk,max_eq_left hp.1]
    simpa using pow_le_pow_left₀ hp.1 hp.2 k

lemma goodMoment_integral (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : LiteralExperiment.GuardData) (b A U ε : ℝ) (k : ℕ)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) :
    (∫ x,goodMoment (RawMixedSource.source i G) i C g b A U ε k x
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N)=
    (∫ x in EntryRawGoodMoments.goodEvent i G g N ε A U,
      deficitMoment k (sampleDeficit i C b g.multiplier x)
        ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N) := by
  rw [← integral_indicator (EntryRawGoodMoments.measurable_goodEvent i G g N ε A U)]
  apply integral_congr_ae
  filter_upwards [usable_ae_good i G g b A U ε hcap] with x hx
  have he : (x∈usable (RawMixedSource.source i G) i g b A U ε) ↔
      x∈EntryRawGoodMoments.goodEvent i G g N ε A U := Iff.of_eq hx
  change (if x∈usable (RawMixedSource.source i G) i g b A U ε then
    deficitMoment k (sampleDeficit i C b g.multiplier x) else 0)=
    (if x∈EntryRawGoodMoments.goodEvent i G g N ε A U then
      deficitMoment k (sampleDeficit i C b g.multiplier x) else 0)
  rw [propext he]

lemma response_zero_of_balanced_nonpos (ν : Measure RowRival) (i : Row) (g : LiteralExperiment.GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs ν i g N C b A U ε c q lo γ w s)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) (hW : balanced i C b x.1 ≤ 0) :
    response ν i C g b A U ε x=0 ∧ ∀ k,goodMoment ν i C g b A U ε k x=0 := by
  have hb : 0 < b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  have hD : sampleDeficit i C b g.multiplier x ≤ 0 := by
    have hh := sample_nonneg i hb g.multiplier x
    dsimp [sampleDeficit]
    linarith
  have hG : ∀ k,goodMoment ν i C g b A U ε k x=0 := by
    intro k
    unfold goodMoment
    split_ifs <;> simp [deficitMoment_eq_zero_of_nonpos k hD]
  refine ⟨?_,hG⟩
  have hp := response_bounds ν i g b A U ε x (C := C)
  have hstrict := response_strict_indicator ν i g h x
  rw [hG 0,deficitMoment_zero] at hstrict
  by_cases hp' : 0 < response ν i C g b A U ε x
  · simp [hp'] at hstrict
  · exact le_antisymm (le_of_not_gt hp') hp.1

section Original
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem original_moderate_response_moments
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m,Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m,∀ᵐ ω ∂μ,B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ,entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b : ℕ → ℝ) (hbt : ∀ m,b m ≤ cutoff i) (hb : Tendsto b atTop (𝓝 (entry i)))
    (g : ℕ → LiteralExperiment.GuardData)
    (hl : Tendsto (fun m => (g m).multiplier) atTop (𝓝 (entry i)))
    (n : ℕ → ℕ) (hnp : ∀ m,4 ≤ n m) (hn : Tendsto n atTop atTop)
    {ε q lo : ℝ} (hε : 0 < ε) (hloEntry : lo < entry i)
    (A γ w s : ℕ → ℝ)
    (hcap : ∀ m,∀ᵐ p ∂joint μ V (B m),p.2 ≤ ReceiptGap.cap i)
    (hfinite : ∀ m,Inputs (RawMixedSource.source i (joint μ V (B m))) i (g m)
      (n m-1) (capacity (n m)) (b m) (A m) (ReceiptGap.cap i) ε
      (eligibleMass μ i V/2) q lo (γ m) (w m) (s m))
    (hmoderate : Tendsto (fun m => -EntryRawCentral.center i (joint μ V (B m)) (n m-1)
      (capacity (n m)) (b m)) atTop atTop)
    {k : ℕ} (hk : k ≤ 2) :
    let G := fun m => joint μ V (B m)
    let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (n m-1)
    let p := fun m => response (RawMixedSource.source i (G m)) i (capacity (n m))
      (g m) (b m) (A m) (ReceiptGap.cap i) ε
    Tendsto (fun m => ((n m-1:ℕ):ℝ)^(k+1)*(theta μ i V B b n m)^(k+2)*
      (∫ x,deficitMoment k (p m x) ∂ P m)/commonFactor μ i V B b n m)
      atTop (𝓝 (limitConstant μ i V*(1/(entry i*reciprocalMean μ i V))^k*(Nat.factorial k:ℝ))) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (hB m)).aemeasurable
  let N := fun m => n m-1
  let C := fun m => capacity (n m)
  let U := ReceiptGap.cap i
  let ν := fun m => RawMixedSource.source i (G m)
  let θ := theta μ i V B b n
  let Q := commonFactor μ i V B b n
  let P := fun m => EntryIIDCentral.rowLaw (ν m) (N m)
  let p := fun m => response (N := N m) (ν m) i (C m) (g m) (b m) (A m) U ε
  let D := fun m => sampleDeficit (N := N m) i (C m) (b m) (g m).multiplier
  let W := fun m (x : EntryIIDCentral.Row (Ω := RowRival) (N m)) => balanced i (C m) (b m) x.1
  let Z := fun m x => deficitMoment k (D m x)
  let ZG := fun m => goodMoment (N := N m) (ν m) i (C m) (g m) (b m) (A m) U ε k
  let κ := reciprocalMean μ i V
  let a0 := 1/(entry i*κ)
  let a := samplingFloor i
  let d := min (q/(2*U)) (κ/2)
  let displacement := xi i/(q/(2*U))
  let r := fun m => EntryModerateProfile.radius (N m)
  let z := fun m => max lo (b m-displacement*r m)
  let R := fun m => rawTilt i (G m) (b m) (-θ m)
  let Pt := fun m => EntryIIDCentral.rowLaw (R m) (N m)
  have hNp : ∀ m,0 < N m := fun m => (hfinite m).rivals_pos
  have hN : Tendsto N atTop atTop := PhysicalRates.rivals_tendsto.comp hn
  have hbp : ∀ m,0 < b m := fun m => (hfinite m).lo_pos.trans_le
    ((hfinite m).lower_price.trans (hfinite m).bid_window.1)
  have hlo : 0 < lo := (hfinite 0).lo_pos
  have hblo : ∀ m,lo ≤ b m := fun m => (hfinite m).lower_price.trans (hfinite m).bid_window.1
  have hU : 0 < U := (ReceiptGap.cap_bounds i).1
  have hq : 0 < q := (hfinite 0).strip_pos
  have hκ : 0 < κ := reciprocalMean_positive μ i V hV hvalue
  have hentry : 0 < entry i := EarlyMean.entry_pos i
  have hd : 0 < d := lt_min (div_pos hq (by positivity)) (by positivity)
  have hdq : d ≤ q/(2*U) := min_le_left _ _
  have hdκ : d ≤ κ := (min_le_right _ _).trans (by linarith)
  have ha0 : 0 < a0 := one_div_pos.mpr (mul_pos (EarlyMean.entry_pos i) hκ)
  have ha := samplingFloor_geometry i
  have hθbounds := fun m => theta_bounds μ i V B b n m
  letI (m : ℕ) : IsProbabilityMeasure (R m) := rawTilt_probability i (G m) (hbp m) (-θ m)
  have htilt := original_moderate_tilt μ i V B hV hB hvalue hadmissible hactive
    b hbp hbt hb n hnp hn hmoderate
  have hθ0 : Tendsto θ atTop (𝓝 0) := htilt.2.1
  have hθN : Tendsto (fun m => θ m*Real.sqrt (N m:ℝ)) atTop atTop := htilt.2.2.1
  have hr0 : Tendsto r atTop (𝓝 0) := EntryModerateProfile.radius_tendsto N hN
  have hz : Tendsto z atTop (𝓝 (entry i)) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => lo) atTop (𝓝 lo)).max
      (hb.sub (hr0.const_mul displacement))
    simpa [z,sub_zero,max_eq_right hloEntry.le] using ht
  have hbMean := EntryModerateReciprocal.actual_test_mean_tendsto μ i V B hV hB hvalue hadmissible hactive
    hlo b b (fun m => -θ m) hbp hblo hb (by simpa using hθ0.neg)
  have hzMean := EntryModerateReciprocal.actual_test_mean_tendsto μ i V B hV hB hvalue hadmissible hactive
    hlo b z (fun m => -θ m) hbp (fun _ => le_max_left _ _) hz (by simpa using hθ0.neg)
  let ER := fun m => EntryModerateReciprocal.event (R m) lo (b m) (z m) (N m)
  let E := fun m => (Prod.fst ⁻¹' ER m : Set (EntryIIDCentral.Row (Ω := RowRival) (N m)))
  have hE : ∀ m,MeasurableSet (E m) := fun m =>
    (EntryModerateReciprocal.measurable_event (R m) lo (b m) (z m) (N m)).preimage measurable_fst
  have hBad : ∀ m,(Pt m).real (E m)ᶜ ≤ 4*Real.exp (-2*Real.sqrt (N m:ℝ)) := by
    intro m
    have hmap : (Pt m).real (E m)ᶜ=(Measure.pi (fun _ : Fin (N m) => R m)).real (ER m)ᶜ := by
      change ((Pt m) (Prod.fst ⁻¹' (ER m)ᶜ)).toReal= _
      have hm : (Pt m).map Prod.fst=Measure.pi (fun _ : Fin (N m) => R m) :=
        (measurePreserving_fst (μ := Measure.pi (fun _ : Fin (N m) => R m))
          (ν := (volume : Measure unitInterval))).map_eq
      rw [← Measure.map_apply measurable_fst (EntryModerateReciprocal.measurable_event _ _ _ _ _).compl,hm]
      rfl
    rw [hmap]
    exact EntryModerateReciprocal.complement_le (R m) hlo (hblo m) (le_max_left _ _) (N m) (hNp m)
  let eK := fun m => EntryModerateReciprocal.error (R m) lo (b m) (z m) a κ (N m)
  have heK := EntryModerateReciprocal.error_tendsto R lo a κ b z N hN hbMean hzMean
  have heK0 := fun m => EntryModerateReciprocal.error_nonneg (R m) hlo ha.1 (b m) (z m) κ (N m)
  let L := 1/(lo*d)+a0
  let eA := fun m => (1/(N m:ℝ)+|b m-entry i| *κ+|b m| *eK m)/((lo*d)*(entry i*κ))
  let e := fun m => (1+2*L)*eA m
  have hL : 0 < L := by dsimp [L]; positivity
  have heA : Tendsto eA atTop (𝓝 0) := by
    have hi : Tendsto (fun m => 1/(N m:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hN)
    simpa [eA] using ((hi.add (((hb.sub_const (entry i)).abs).mul_const κ)).add (hb.abs.mul heK)).div_const ((lo*d)*(entry i*κ))
  have he : Tendsto e atTop (𝓝 0) := by simpa [e] using heA.const_mul (1+2*L)
  have he0 : ∀ m,0 ≤ e m := by
    intro m
    have := heK0 m
    dsimp [e,eA]
    positivity
  let F := fun m x => |(N m:ℝ)^k*deficitMoment k (p m x)-a0^k*ZG m x|
  have hZm : ∀ m,Measurable (Z m) := fun m => measurable_deficitMoment
    (measurable_sampleDeficit i (C m) (b m) (g m).multiplier) k
  have hpm : ∀ m,Measurable (fun x => deficitMoment k (p m x)) := fun m =>
    measurable_deficitMoment (measurable_response (ν m) i (C m) (g m) (b m) (A m) U ε) k
  have hZgm : ∀ m,Measurable (ZG m) := fun m => measurable_goodMoment (ν m) i (C m) (g m) (b m) (A m) U ε k
  have hFm : ∀ m,Measurable (F m) := fun m => (((hpm m).const_mul _).sub ((hZgm m).const_mul (a0^k))).abs
  have hZb : ∀ m x,Z m x∈Icc (0:ℝ) ((N m:ℝ)^k) := by
    intro m x
    refine ⟨deficitMoment_nonneg _ _,?_⟩
    have hC : (C m:ℝ)+1 ≤ N m := by
      exact_mod_cast Nat.succ_le_of_lt (PhysicalRates.capacity_strictly_below_rivals (hnp m))
    exact ((le_abs_self _).trans (sampleDeficit_moment_bound i (C m) (hbp m) (g m).multiplier k x)).trans
      (pow_le_pow_left₀ (by positivity) hC k)
  have hFbound : ∀ m x,F m x∈Icc (0:ℝ) ((1+a0^k)*(N m:ℝ)^k) := by
    intro m x
    refine ⟨abs_nonneg _,?_⟩
    have hpB := responseMoment_bounds (ν m) i (g m) (b m) (A m) U ε k x (C := C m)
    have hzG := (goodMoment_le (ν m) i (C m) (g m) (b m) (A m) U ε k x).trans (hZb m x).2
    have hz0 := goodMoment_nonneg (ν m) i (C m) (g m) (b m) (A m) U ε k x
    have hh := abs_sub ((N m:ℝ)^k*deficitMoment k (p m x)) (a0^k*ZG m x)
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hpB.1),
      abs_of_nonneg (mul_nonneg (pow_nonneg ha0.le _) hz0)] at hh
    have h1 := mul_le_mul_of_nonneg_left hpB.2 (pow_nonneg (Nat.cast_nonneg (N m)) k)
    have h2 := mul_le_mul_of_nonneg_left hzG (pow_nonneg ha0.le k)
    dsimp [F]
    nlinarith
  have hZzero : ∀ m x,W m x ≤ 0 → Z m x=0 := by
    intro m x hx
    apply deficitMoment_eq_zero_of_nonpos
    have hs := sample_nonneg i (hbp m) (g m).multiplier x
    dsimp [W,D,sampleDeficit] at *
    linarith
  have hFzero : ∀ m x,W m x ≤ 0 → F m x=0 := by
    intro m x hx
    have hh := response_zero_of_balanced_nonpos (ν m) i (g m) (hfinite m) x hx
    dsimp [F,p,ZG]
    rw [hh.1,hh.2 k,deficitMoment_eq_zero_of_nonpos k le_rfl]
    simp
  have hrow : ∀ᶠ m in atTop,∀ᵐ x ∂ Pt m,∀ j,a ≤ hs i (b m) x.1 j := by
    filter_upwards [hb.eventually (Ioi_mem_nhds ha.2.2.2)] with m hm
    have hh := EntryModerateProfile.actual_h_profile_ae i (G m) (hbp m) ha.1 ha.2.1 ha.2.2.1
      hm.le (hcap m) (-θ m) (N m)
    exact ((measurePreserving_fst (μ := Measure.pi (fun _ : Fin (N m) => R m))
      (ν := (volume : Measure unitInterval))).quasiMeasurePreserving.ae hh).mono fun x hx j => (hx j).1
  have hcore : ∀ᶠ m in atTop,∀ᵐ x ∂ Pt m,x∈E m → W m x ≤ r m*(N m:ℝ) → F m x ≤ e m*Z m x := by
    filter_upwards [hrow] with m hm
    filter_upwards [hm] with x hx hxe hWx
    have hident := rescaled_response_moment (ν m) i (g m) (hfinite m) hd hdq k x
    have heq : F m x=|(coefficient (N m) (b m) d (slope (ν m) i (C m) (g m) (b m) (A m) U ε x/(N m:ℝ)))^k-a0^k| *ZG m x := by
      dsimp [F,p]
      rw [hident,← sub_mul,abs_mul,abs_of_nonneg (goodMoment_nonneg _ _ _ _ _ _ _ _ _ x)]
    rw [heq]
    by_cases hu : x∈usable (ν m) i (g m) (b m) (A m) U ε
    · by_cases hpD : 0 < D m x
      · have hK := successful_reciprocal_error (κ := κ) (ν m) i (g m) (hfinite m) ha.1
          (EntryModerateProfile.radius_pos (hNp m)).le x hu hx hpD hWx
        have hE0 := EntryModerateReciprocal.event_test_error (R m) hlo (N m) x.1 hxe 0 (κ := κ)
        have hE1 := EntryModerateReciprocal.event_test_error (R m) hlo (N m) x.1 hxe 1 (κ := κ)
        have hKe : |slope (ν m) i (C m) (g m) (b m) (A m) U ε x/(N m:ℝ)-κ| ≤ eK m := by
          dsimp [EntryModerateReciprocal.tests] at hE0 hE1
          have hh' := hK.trans (add_le_add (add_le_add hE0 hE1) le_rfl)
          convert! hh' using 1; dsimp [eK,EntryModerateReciprocal.error,z,r,displacement]; ring
        have hAe := coefficient_error (N := N m) (k := slope (ν m) i (C m) (g m) (b m) (A m) U ε x/(N m:ℝ))
          hlo (hblo m) hd (EarlyMean.entry_pos i) hκ hdκ
        have haerr : |coefficient (N m) (b m) d (slope (ν m) i (C m) (g m) (b m) (A m) U ε x/(N m:ℝ))-a0| ≤ eA m := by
          apply hAe.trans
          dsimp [eA,a0]
          exact div_le_div_of_nonneg_right
            (add_le_add le_rfl (mul_le_mul_of_nonneg_left hKe (abs_nonneg (b m))))
            (mul_pos (mul_pos hlo hd) (mul_pos (EarlyMean.entry_pos i) hκ)).le
        have hcoef := coefficient_bounds (N := N m) (k := slope (ν m) i (C m) (g m) (b m) (A m) U ε x/(N m:ℝ)) hlo (hblo m) hd
        have hpow := small_power_error (show |coefficient (N m) (b m) d (slope (ν m) i (C m) (g m) (b m) (A m) U ε x/(N m:ℝ))| ≤ L by
          rw [abs_of_pos hcoef.1]
          exact hcoef.2.trans (by dsimp[L]; linarith))
          (show |a0| ≤ L by rw [abs_of_pos ha0]; dsimp[L]; linarith [one_div_pos.mpr (mul_pos hlo hd)]) k hk
        have hpowe : |(coefficient (N m) (b m) d (slope (ν m) i (C m) (g m) (b m) (A m) U ε x/(N m:ℝ)))^k-a0^k| ≤ e m :=
          hpow.trans (mul_le_mul_of_nonneg_left haerr (by dsimp[L]; positivity))
        have hzg : ZG m x=Z m x := by simp [ZG,goodMoment,hu,Z,D]
        rw [hzg]
        exact mul_le_mul_of_nonneg_right hpowe (hZb m x).1
      · have hz : ZG m x=0 := by simp [ZG,goodMoment,hu,D,deficitMoment_eq_zero_of_nonpos k (le_of_not_gt hpD)]
        rw [hz,mul_zero]
        exact mul_nonneg (he0 m) (hZb m x).1
    · have hz : ZG m x=0 := by simp [ZG,goodMoment,hu]
      rw [hz,mul_zero]
      exact mul_nonneg (he0 m) (hZb m x).1
  have hfull := original_joint_factorial_moments μ i V B hV hB hvalue hadmissible hactive hcap
    b (fun m => (g m).multiplier) hbp hbt
    (fun m => by have hm := (hfinite m).prefix.lower_pos; have hr := (hfinite m).radius_pos; linarith)
    hb hl n hnp hn hmoderate hk
  have hZabs : ∀ m x,|Z m x| ≤ (N m:ℝ)^k := fun m x => by rw [abs_of_nonneg (hZb m x).1]; exact (hZb m x).2
  have hmain : Tendsto (fun m => (N m:ℝ)*θ m^(k+2)*
      (∫ x,Real.exp (-θ m*W m x)*Z m x ∂ Pt m)) atTop
        (𝓝 (limitConstant μ i V*(Nat.factorial k:ℝ))) := by
    apply hfull.congr
    intro m
    rw [exact_reverse_seed_integral i (G m) (C := C m) (hbp m) (hθbounds m).1
      (Z m) (hZm m) (hZabs m)]
    field_simp [(Real.exp_pos _).ne']
    ring
  have hrelative := relative_weighted_error Pt N hNp hN θ
    (fun m => ⟨(hθbounds m).1,(hθbounds m).2.le⟩) hθN W Z F
    (fun m => (measurable_balanced i (C m) (b m)).comp measurable_fst)
    hZm hFm k (B := 1+a0^k) (C := 4) (by positivity) (by norm_num)
    hZb hFbound hZzero hFzero E hE hBad e he0 he hcore hmain
  have hGood := original_good_joint_factorial_moments μ i V B hV hB hvalue hadmissible hactive hcap
    b hbp hbt hb g (fun m => (hfinite m).prefix.lower_pos)
    (fun m => by have hm := (hfinite m).prefix.lower_pos; have hr := (hfinite m).radius_pos; linarith)
    (fun m => (hfinite m).prefix.rejectionScale_pos) hl
    (fun m => by have hm := (hfinite m).prefix.lower_pos; have hr := (hfinite m).radius_pos; linarith)
    n hnp hn hmoderate hε A (fun _ => U) hk
  have hGI (m) : Integrable (ZG m) (P m) :=
    Integrable.of_mem_Icc 0 ((N m:ℝ)^k) (hZgm m).aemeasurable (ae_of_all _ fun x =>
      ⟨goodMoment_nonneg _ _ _ _ _ _ _ _ _ _,(goodMoment_le _ _ _ _ _ _ _ _ _ _).trans (hZb m x).2⟩)
  have hpI (m) : Integrable (fun x => deficitMoment k (p m x)) (P m) :=
    Integrable.of_mem_Icc 0 1 (hpm m).aemeasurable
      (ae_of_all _ (responseMoment_bounds (ν m) i (g m) (b m) (A m) U ε k))
  have hGood' : Tendsto (fun m => (N m:ℝ)*θ m^(k+2)*(∫ x,ZG m x ∂ P m)/Q m)
      atTop (𝓝 (limitConstant μ i V*(Nat.factorial k:ℝ))) := by
    apply hGood.congr
    intro m
    rw [goodMoment_integral i (G m) (g m) (b m) (A m) U ε k (hcap m)]
  let T := fun m => (N m:ℝ)^(k+1)*θ m^(k+2)*(∫ x,deficitMoment k (p m x) ∂ P m)/Q m
  let T0 := fun m => a0^k*((N m:ℝ)*θ m^(k+2)*(∫ x,ZG m x ∂ P m)/Q m)
  have herror : Tendsto (fun m => |T m-T0 m|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) ?_ hrelative
    intro m
    have hQp : 0 < Q m := commonFactor_positive μ i V B b n m
    have hfI : Integrable (fun x => (N m:ℝ)^k*deficitMoment k (p m x)-a0^k*ZG m x) (P m) :=
      ((hpI m).const_mul _).sub ((hGI m).const_mul _)
    have habs := abs_integral_le_integral_abs
      (f := fun x => (N m:ℝ)^k*deficitMoment k (p m x)-a0^k*ZG m x) (μ := P m)
    rw [integral_sub ((hpI m).const_mul _) ((hGI m).const_mul _),integral_const_mul,integral_const_mul] at habs
    have hreverse := exact_reverse_seed_integral i (G m) (C := C m) (hbp m) (hθbounds m).1
      (F m) (hFm m) (fun x => by rw [abs_of_nonneg (hFbound m x).1]; exact (hFbound m x).2)
    have hscaled := mul_le_mul_of_nonneg_left habs
      (show 0 ≤ (N m:ℝ)*θ m^(k+2)/Q m by have := (hθbounds m).1; positivity)
    dsimp [T,T0]
    rw [show (N m:ℝ)^(k+1)*θ m^(k+2)*(∫ x,deficitMoment k (p m x) ∂ P m)/Q m-
      a0^k*((N m:ℝ)*θ m^(k+2)*(∫ x,ZG m x ∂ P m)/Q m)=
      ((N m:ℝ)*θ m^(k+2)/Q m)*((N m:ℝ)^k*(∫ x,deficitMoment k (p m x) ∂ P m)-
        a0^k*(∫ x,ZG m x ∂ P m)) by rw[pow_succ]; ring,
      abs_mul,abs_of_nonneg (show 0 ≤ (N m:ℝ)*θ m^(k+2)/Q m by have := (hθbounds m).1; positivity)]
    apply hscaled.trans_eq
    change (N m:ℝ)*θ m^(k+2)/Q m*(∫ x,F m x ∂ P m)=_
    rw [hreverse]
    dsimp [Q,commonFactor]
    field_simp [(Real.exp_pos _).ne']
    ring
  have hT0 := hGood'.const_mul (a0^k)
  have hT := EntryRawGoodMoments.tendsto_of_abs_sub_tendsto hT0 herror
  have hout : a0^k*(limitConstant μ i V*(Nat.factorial k:ℝ))=
      limitConstant μ i V*(1/(entry i*reciprocalMean μ i V))^k*(Nat.factorial k:ℝ) := by
    dsimp [a0,κ]
    ring
  simpa only [hout] using hT

end Original
end FCAppendix.Affine.Uniform06.EntryLiteralModerate
