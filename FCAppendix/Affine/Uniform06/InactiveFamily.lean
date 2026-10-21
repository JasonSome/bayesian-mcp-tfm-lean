import FCAppendix.Affine.Uniform06.LiteralRemoteInactive

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.InactiveFamily
open MeasureTheory Set Filter Topology LowBody
open Uniform07 LiteralExperiment LiteralPrefixStieltjes LiteralRankIC
open SourceRankRates PureRankCounts PureRankProbability LiteralWeakRent
open EarlyCoarseUniform LiteralRemoteInactive LowInactiveIdentity

theorem eventually_pure_half (i : Row) :
    ∀ᶠ m : ℕ in atTop,0 < Lm i m ∧
      LiteralLowDuplicate.pureRare m ≤ Real.exp (-(6/1000000:ℝ)*m)*Lm i m ∧
      ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G) (b : ℝ),0 < b → G {b}=0 →
        sourceRank (cutoff i) G b ≤ RankCutoff.Mstar i →
        Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) (sourceRank (cutoff i) G b)/2 ≤
          qPure (m-1) (capacity m) (kappa i) (cutoff i) G b := by
  obtain ⟨γ,hγ,hrel⟩ := eventually_source_pure_relative i
  have ht : Tendsto (fun m : ℕ => Real.exp (-γ*m)+Real.exp (-(6/1000000:ℝ)*m))
      atTop (𝓝 0) := by
    convert! (tendsto_exp_affine_nat hγ 0).add
      (tendsto_exp_affine_nat (by norm_num : (0:ℝ) < 6/1000000) 0) using 1
    · funext m
      congr 1 <;> congr 1 <;> ring
    · simp
  filter_upwards [hrel,eventually_Lm_lower i,
    ht.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with m hm hL he
  have hL0 : 0 < Lm i m := (Real.exp_pos _).trans_le hL
  have hrare : LiteralLowDuplicate.pureRare m ≤ Real.exp (-(6/1000000:ℝ)*m)*Lm i m := by
    have hh := mul_le_mul_of_nonneg_left hL (Real.exp_pos (-(6/1000000:ℝ)*m)).le
    convert! hh using 1
    unfold LiteralLowDuplicate.pureRare
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨hL0,hrare,?_⟩
  intro G hG b hb ha hM
  letI := hG
  let Q := Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) (sourceRank (cutoff i) G b)
  have hQ : 0 < Q := hL0.trans_le
    (unilateral_le_pureRank (cutoff_pos i).le (cutoff_lt_one i) G b (m-1) (capacity m))
  have hh := (abs_le.mp (hm G hG b hb ha hM)).1
  have hratio : 1/2 ≤ qPure (m-1) (capacity m) (kappa i) (cutoff i) G b/Q := by
    linarith
  have hh' := (le_div_iff₀ hQ).mp hratio
  linarith

theorem eventual_scalar_contradiction (i : Row) {ε A τ Θ : ℝ}
    (hε : 0 < ε) (hA : 0 < A) (hτ : 0 < τ) :
    ∀ᶠ m : ℕ in atTop,
      40000/(m:ℝ)+cutoff i*Real.exp (-(6/1000000:ℝ)*m) ≤ ε/8 ∧
      cutoff i*A^2/((m-1:ℕ):ℝ) ≤ ε/2 ∧
      4*cutoff i/ε < (1/A^2)*Real.exp (((m-1:ℕ):ℝ)*gainConstant i τ Θ*(ε/4)) := by
  have hN : Tendsto (fun m : ℕ => ((m-1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp PhysicalRates.rivals_tendsto
  have he : Tendsto (fun m : ℕ => Real.exp (-(6/1000000:ℝ)*m)) atTop (𝓝 0) := by
    convert! tendsto_exp_affine_nat (by norm_num : (0:ℝ) < 6/1000000) 0 using 1
    funext m
    congr 1
    ring
  have hc : Tendsto (fun m : ℕ => 40000/(m:ℝ)+cutoff i*Real.exp (-(6/1000000:ℝ)*m))
      atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add (he.const_mul (cutoff i))
  have hd : Tendsto (fun m : ℕ => cutoff i*A^2/((m-1:ℕ):ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have hκ : 0 < gainConstant i τ Θ*(ε/4) := mul_pos (gainConstant_pos i hτ) (by positivity)
  have harg : Tendsto (fun m : ℕ => ((m-1:ℕ):ℝ)*gainConstant i τ Θ*(ε/4)) atTop atTop := by
    convert! hN.const_mul_atTop hκ using 1
    funext m
    ring
  have hg : Tendsto (fun m : ℕ => (1/A^2)*Real.exp
      (((m-1:ℕ):ℝ)*gainConstant i τ Θ*(ε/4))) atTop atTop :=
    (Real.tendsto_exp_atTop.comp harg).const_mul_atTop (by positivity)
  filter_upwards [hc.eventually_lt_const (by positivity : (0:ℝ) < ε/8),
    hd.eventually_lt_const (by positivity : (0:ℝ) < ε/2),hg.eventually_gt_atTop (4*cutoff i/ε)]
    with m hc hd hg
  exact ⟨hc.le,hd.le,hg⟩

section Family
variable (C : ℕ → Type*) (G : (m : ℕ) → C m → ProbabilityMeasure (ℝ × ℝ))
variable (g : (m : ℕ) → C m → GuardData)
variable (cm : (m : ℕ) → C m → (Fin (m-1) → Fin 4) → ℝ)

theorem common_used_inactive (i : Row) {K : ℝ} (hK : entry i < K)
    (hvalue : ∀ m (E : C m),(G m E:Measure (ℝ × ℝ)).map Prod.fst=
      LowChernoff.conditionalValueLaw i)
    (hatom : ∀ m (E : C m) b,(G m E:Measure (ℝ × ℝ)).map Prod.snd {b}=0)
    (hcommon : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p ∈ usedSet i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) (ReceiptGap.cap i))
    (hactive : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e)
    (hroot : ∀ ε > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      |(g m E).multiplier-entry i| < ε)
    (hguard : ∀ᶠ m in atTop,∀ E : C m,(g m E).radius ≤ cutoff i/100 ∧
      PrefixConditions (xi i) (g m E) K)
    {d ε : ℝ} (hd : 0 < d) (hdmax : d ≤ x i-1/2) (hε : 0 < ε) :
    ∀ᶠ m in atTop,∀ E : C m,∀ p ∈ usedSet i m (G m E:Measure (ℝ × ℝ))
      (g m E) (cm m E) (ReceiptGap.cap i), p.1 ≤ (x i-d)*cutoff i → |p.2-p.1| < ε := by
  have hbox : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p ∈ EarlyJointCompactness.box (cutoff i) (ReceiptGap.cap i) := by
    intro m E
    exact (hcommon m E).mono fun p hp => ⟨hp.1,hp.2.1.le,hp.2.2.1.2.trans (min_le_right _ _)⟩
  have hbid : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.2 ≤ p.1 :=
    fun m E => (hcommon m E).mono fun p hp => hp.2.2.1.2.trans (min_le_left _ _)
  have hgco : ∀ᶠ m in atTop,∀ E : C m,(g m E).radius ≤ cutoff i/100 ∧
      0 < (g m E).margin ∧ 0 < (g m E).population ∧ 0 < (g m E).requiredDemand := by
    filter_upwards [hguard] with m hm E
    exact ⟨(hm E).1,(hm E).2.margin_pos,(hm E).2.population_pos,(hm E).2.requiredDemand_pos⟩
  obtain ⟨θ,τ,Θ,A,hτ,hΘ,hcoarse⟩ := source_uniform_coarse C G g cm i hd hdmax
    hvalue hbox hbid hactive hroot hgco
  have hA : 0 < (A:ℝ)+1 := by positivity
  have ha : 0 < EarlyRankCeiling.ceilingValue i-entry i :=
    sub_pos.mpr (EarlyRankCeiling.ceilingValue_bounds i).1.1
  have hactiveStrip := hactive (EarlyRankCeiling.ceilingValue i-entry i) ha
    (cutoff i/10000) (div_pos (cutoff_pos i) (by norm_num))
  have heActive : entry i+(EarlyRankCeiling.ceilingValue i-entry i)=EarlyRankCeiling.ceilingValue i := by ring
  have hscalar := eventual_scalar_contradiction i (Θ := Θ) hε hA hτ
  have hlow := (lowInactiveError_tendsto_zero i).eventually_lt_const hε
  have hentryGap : (501/1000:ℝ)*cutoff i+cutoff i/100 < entry i-cutoff i/200 := by
    have hx : (501/1000:ℝ)+1/100 < x i-1/200 := by cases i <;> norm_num [x,xQ]
    have hh := mul_lt_mul_of_pos_right hx (cutoff_pos i)
    simpa only [entry,sub_mul,add_mul,div_mul_eq_mul_div,one_mul] using hh
  filter_upwards [hcoarse,hguard,hactiveStrip,hscalar,eventually_pure_half i,hlow,
    eventually_source_low_used_bid_error i,hroot (cutoff i/200) (div_pos (cutoff_pos i) (by norm_num)),
    eventually_ge_atTop (4:ℕ)] with m hc hg ha hs hpure hl hlow hrootm hm
  intro E p hp hpv
  have hpEntry : p.1 < entry i := by
    have hh : (x i-d)*cutoff i < entry i := by
      unfold entry
      nlinarith [mul_pos hd (cutoff_pos i)]
    exact hpv.trans_lt hh
  have hpK := hpEntry.trans hK
  have hpbv : p.2 ≤ p.1 := hp.2.2.1.2.trans (min_le_left _ _)
  have habs : |p.2-p.1|=p.1-p.2 := by rw [abs_of_nonpos (sub_nonpos.mpr hpbv)]; ring
  rw [habs]
  by_cases hlowbid : p.2 ≤ LowRankMeasures.lowEnd i
  · have hL : LowRankMeasures.extensionEnd i ≤ (g m E).multiplier-(g m E).radius := by
      have hr := (abs_lt.mp (hrootm E)).1
      have ha := (hg E).1
      change (501/1000:ℝ)*cutoff i ≤ (g m E).multiplier-(g m E).radius
      linarith
    exact (hlow (G m E:Measure (ℝ × ℝ)) inferInstance (hvalue m E) (hatom m E)
      (g m E) K (ReceiptGap.cap i) (cm m E) (ReceiptGap.cap_bounds i).1.le (hg E).2 hL
      (hcommon m E) p hp hpK hpEntry.le hlowbid).2.trans_lt hl
  · by_contra hn
    have hrent : ε ≤ p.1-p.2 := le_of_not_gt hn
    have hhalf : cutoff i/2 ≤ p.2 := by
      change ¬ p.2 ≤ cutoff i/2 at hlowbid
      exact (lt_of_not_ge hlowbid).le
    have hlocal : ∀ z ∈ Icc (p.2/cutoff i) ((p.2+ε/4)/cutoff i),
        z ∈ Icc (1/2:ℝ) (x i-d) := by
      intro z hz
      refine ⟨?_,?_⟩
      · exact ((le_div_iff₀ (cutoff_pos i)).mpr (by nlinarith)).trans hz.1
      · apply hz.2.trans
        apply (div_le_iff₀ (cutoff_pos i)).mpr
        linarith
    apply actual_positive_rent_contradiction i hm (G m E:Measure (ℝ × ℝ))
      (hvalue m E) (hatom m E)
      (by simpa only [heActive] using ha E) (g m E) (hg E).2 (cm m E)
      (hcommon m E) hp hpK hpEntry hhalf hε hA hτ hrent (θ m E)
      (fun z hz => hc E z (hlocal z hz)) hpure.1 hpure.2.1
      (fun b hb hM => hpure.2.2 ((G m E:Measure (ℝ × ℝ)).map Prod.snd)
        (Measure.isProbabilityMeasure_map measurable_snd.aemeasurable) b hb (hatom m E b) hM)
      hs.1 hs.2.1 hs.2.2

theorem original_common_conull_inactive (i : Row) {K : ℝ} (hK : entry i < K)
    (hvalue : ∀ m (E : C m),(G m E:Measure (ℝ × ℝ)).map Prod.fst=
      LowChernoff.conditionalValueLaw i)
    (hatom : ∀ m (E : C m) b,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hmenu : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p.2 ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)))
    (hIC : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      ∀ a ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)),
        Rank.payoff (eta i) p.1 a (sourceSuccess i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) a)
          (sourceDuplicate i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) a) ≤
        Rank.payoff (eta i) p.1 p.2 (sourceSuccess i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) p.2)
          (sourceDuplicate i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) p.2))
    (hactive : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e)
    (hroot : ∀ ε > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      |(g m E).multiplier-entry i| < ε)
    (hguard : ∀ᶠ m in atTop,∀ E : C m,(g m E).radius ≤ cutoff i/100 ∧
      PrefixConditions (xi i) (g m E) K)
    {d ε : ℝ} (hd : 0 < d) (hdmax : d ≤ x i-1/2) (hε : 0 < ε) :
    ∀ᶠ m in atTop,∀ E : C m,∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p.1 ≤ (x i-d)*cutoff i → |p.2-p.1| < ε := by
  have hu := fun m E => usedSet_full i m (G m E:Measure (ℝ × ℝ)) (hvalue m E) (hatom m E)
    (g m E) (cm m E) (ReceiptGap.cap i) (hmenu m E) (hIC m E)
  filter_upwards [common_used_inactive C G g cm i hK hvalue hatom hu hactive hroot hguard hd hdmax hε]
    with m hm E
  exact (hu m E).mono fun p hp hpv => hm E p hp hpv

end Family
end FCAppendix.Affine.Uniform06.InactiveFamily
