import FCAppendix.Affine.Hybrid.Finishing01ClearingCounts
import FCAppendix.Affine.Hybrid.Finishing01ClearingFamily

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

namespace Primitives
variable (P:Primitives)

lemma physical_count_nonneg {N:ℕ} (c:ℕ) (kind:Fin N→ Fin 4)
    (b:P.Bid) (rows:ActiveCountRows N) (hr:∀ j,rows.2 j∈ Icc P.L P.U) (k:Fin 3) :
    0≤ activePhysicalPatternCountMass P.xi P.z P.L P.U c kind b rows k := by
  unfold activePhysicalPatternCountMass
  dsimp only
  split_ifs with hg hequal
  · unfold sourceCountMass FiniteLaw.expect
    apply Finset.sum_nonneg
    intro E _
    by_cases hE:(sourceOwnersLaw (activePhysicalActiveBids kind (0,b,rows))
        (activePatternOwner c P.z kind 0) (activePatternOwner c P.z kind 1)).mass E=0
    · simp [hE]
    · have hb:∀ i,activePhysicalActiveBids kind (0,b,rows) i∈ Icc P.L P.U := by
        intro i
        rcases Fin.eq_zero_or_eq_succ i.val with hi | ⟨k,hk⟩
        · simpa only [activePhysicalActiveBids,hi,Fin.cases_zero] using b.property
        · simpa only [activePhysicalActiveBids,hk,Fin.cases_succ] using hr k
      obtain ⟨Q,hqx,hqb,hq0,hq1,hqr,_⟩:=activePattern_guardedData
        P.xi_pos P.xi_lt_one P.L_pos c P.z kind hg _ hb E.1 E.2 hE
      have hq:=Q.exposure_interior (activePatternFocal kind)
      simp only [GuardedData.multiplier,GuardedData.mixed,hqx,hqb,hq0,hq1,hqr] at hq
      apply mul_nonneg (FiniteLaw.nonneg _ _)
      unfold ownerSetCountMass
      dsimp only
      split_ifs
      · unfold pointMass
        split_ifs <;> norm_num
      · exact binomialTwoMass_nonneg ⟨hq.1.le,hq.2.le⟩ k
  · have hq:=EqualCapacity.positiveMarginal_spec P.xi (activePatternTemplate c kind).residual₀ P.xi_pos P.xi_lt_one
      (activePhysicalBids kind (0,b,rows))
    exact binomialTwoMass_nonneg ⟨hq.1 0,hq.2.1 0⟩ k
  · unfold pointMass
    split_ifs <;> norm_num

lemma physical_count_le_one {N:ℕ} (c:ℕ) (kind:Fin N→ Fin 4)
    (b:P.Bid) (rows:ActiveCountRows N) (hr:∀ j,rows.2 j∈ Icc P.L P.U) (k:Fin 3) :
    activePhysicalPatternCountMass P.xi P.z P.L P.U c kind b rows k≤1 := by
  rw [←activePhysicalPatternCountMass_total P.xi P.z P.L P.U c kind b rows]
  exact Finset.single_le_sum (fun j _=> P.physical_count_nonneg c kind b rows hr j) (Finset.mem_univ k)

lemma measurable_physical_count {N:ℕ} (c:ℕ) (kind:Fin N→ Fin 4) (j:Fin 3) :
    Measurable (fun t:P.Bid×ActiveCountRows N=>
      activePhysicalPatternCountMass P.xi P.z P.L P.U c kind t.1 t.2 j) := by
  have he:∀ t:P.Bid×ActiveCountRows N,
      activePhysicalPatternCountMass P.xi P.z P.L P.U c kind t.1 t.2 j=
      reconstructCountMass P.eta t.1
        (activePhysicalPatternPayoff P.xi P.z P.L P.U c kind (0,t.1,t.2))
        (activePhysicalPatternPayoff P.xi P.z P.L P.U c kind (1,t.1,t.2)) j := by
    intro t
    exact congrFun (activePhysicalPatternCountMass_reconstruct P.xi P.z P.L P.U c kind
      t.1 t.2 P.eta_pos.ne' (P.bid_pos t.1).ne') j
  have hm (v:ℝ):Measurable (fun t:P.Bid×ActiveCountRows N=>
      activePhysicalPatternPayoff P.xi P.z P.L P.U c kind (v,t.1,t.2)) :=
    (measurable_activePhysicalPatternPayoff P.xi_pos P.xi_lt_one P.z P.L P.U c kind).comp
      (by fun_prop)
  simp_rw [he]
  unfold reconstructCountMass
  dsimp only
  split_ifs <;> fun_prop

def patternCountInterim {N:ℕ} (c:ℕ) (kind:Fin N→ Fin 4) (F G:Measure ℝ)
    (b:P.Bid) (j:Fin 3) : ℝ :=
  ∫rows:ActiveCountRows N,activePhysicalPatternCountMass P.xi P.z P.L P.U c kind b rows j
    ∂(Measure.pi (fun _:Fin N=> F)).prod (Measure.pi (fun _:Fin N=> G))

def actualCountInterim (N c:ℕ) (F G:Measure ℝ) (b:P.Bid) (j:Fin 3) : ℝ :=
  (CommonList.iid P.categories N).expect (fun kind=> P.patternCountInterim c kind F G b j)

lemma integrable_physical_count {N:ℕ} (c:ℕ) (kind:Fin N→ Fin 4)
    (F G:Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hG:∀ᵐb∂G,b∈ Icc P.L P.U) (b:P.Bid) (j:Fin 3) :
    Integrable (fun rows:ActiveCountRows N=>
      activePhysicalPatternCountMass P.xi P.z P.L P.U c kind b rows j)
      ((Measure.pi (fun _:Fin N=> F)).prod (Measure.pi (fun _:Fin N=> G))) := by
  apply Integrable.of_bound
    ((P.measurable_physical_count c kind j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
  have hr:∀ᵐrows:ActiveCountRows N∂
      (Measure.pi (fun _:Fin N=> F)).prod (Measure.pi (fun _:Fin N=> G)),
      ∀ k,rows.2 k∈ Icc P.L P.U :=
    (measurePreserving_snd (μ:=Measure.pi (fun _:Fin N=> F)) (ν:=Measure.pi (fun _:Fin N=> G))).quasiMeasurePreserving.ae
      (Finishing01Menus.ae_iid_box G hG)
  filter_upwards [hr] with rows hrows
  change ‖activePhysicalPatternCountMass P.xi P.z P.L P.U c kind b rows j‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (P.physical_count_nonneg c kind b rows hrows j)]
  exact P.physical_count_le_one c kind b rows hrows j

lemma patternCountInterim_total {N:ℕ} (c:ℕ) (kind:Fin N→ Fin 4)
    (F G:Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hG:∀ᵐb∂G,b∈ Icc P.L P.U) (b:P.Bid) :
    ∑j:Fin 3,P.patternCountInterim c kind F G b j=1 := by
  unfold patternCountInterim
  rw [←integral_finsetSum _ (fun j _=> P.integrable_physical_count c kind F G hG b j)]
  simp only [activePhysicalPatternCountMass_total,integral_const,probReal_univ,one_smul]

lemma actualCountInterim_total (N c:ℕ) (F G:Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hG:∀ᵐb∂G,b∈ Icc P.L P.U) (b:P.Bid) :
    ∑j:Fin 3,P.actualCountInterim N c F G b j=1 := by
  unfold actualCountInterim FiniteLaw.expect
  rw [Finset.sum_comm]
  simp only [←Finset.mul_sum,P.patternCountInterim_total c _ F G hG b,mul_one,FiniteLaw.total]

lemma actualCountInterim_mem (N c:ℕ) (F G:Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hG:∀ᵐb∂G,b∈ Icc P.L P.U) (b:P.Bid) (j:Fin 3) :
    P.actualCountInterim N c F G b j∈ Icc (0:ℝ) 1 := by
  have hnonneg:∀ j:Fin 3,0≤ P.actualCountInterim N c F G b j := by
    intro j
    unfold actualCountInterim FiniteLaw.expect
    apply Finset.sum_nonneg
    intro kind _
    apply mul_nonneg (FiniteLaw.nonneg _ _)
    apply integral_nonneg_of_ae
    have hr:∀ᵐrows:ActiveCountRows N∂
        (Measure.pi (fun _:Fin N=> F)).prod (Measure.pi (fun _:Fin N=> G)),
        ∀ k,rows.2 k∈ Icc P.L P.U :=
      (measurePreserving_snd (μ:=Measure.pi (fun _:Fin N=> F)) (ν:=Measure.pi (fun _:Fin N=> G))).quasiMeasurePreserving.ae
        (Finishing01Menus.ae_iid_box G hG)
    exact hr.mono fun rows hrows=> P.physical_count_nonneg c kind b rows hrows j
  refine ⟨hnonneg j,?_⟩
  rw [←P.actualCountInterim_total N c F G hG b]
  exact Finset.single_le_sum (fun k _=> hnonneg k) (Finset.mem_univ j)

lemma measurable_actualCountInterim (N c:ℕ) (F G:Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] (j:Fin 3) :
    Measurable (fun b:P.Bid=> P.actualCountInterim N c F G b j) := by
  unfold actualCountInterim FiniteLaw.expect patternCountInterim
  apply Finset.measurable_sum
  intro kind _
  exact measurable_const.mul (P.measurable_physical_count c kind j).stronglyMeasurable.integral_prod_right'.measurable

lemma patternCountInterim_payoff {N:ℕ} (c:ℕ) (kind:Fin N→ Fin 4)
    (F G:Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hG:∀ᵐb∂G,b∈ Icc P.L P.U) (v:ℝ) (b:P.Bid) :
    countPayoff P.eta v b (P.patternCountInterim c kind F G b)=
      Finishing01Menus.patternInterim P.xi P.z P.L P.U c kind F G v b := by
  have h1:=P.integrable_physical_count c kind F G hG b 1
  have h2:=P.integrable_physical_count c kind F G hG b 2
  have hs:=integral_sub ((h1.add h2).const_mul (v-b)) (h2.const_mul (P.eta*b))
  dsimp only [Pi.add_apply] at hs
  simp only [integral_const_mul,integral_add h1 h2] at hs
  unfold countPayoff patternCountInterim Finishing01Menus.patternInterim
  rw [←hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun rows=>
    activePhysicalPatternCountMass_payoff P.xi P.z P.L P.U c kind v b rows

lemma actualCountInterim_payoff (N c:ℕ) (F G:Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hG:∀ᵐb∂G,b∈ Icc P.L P.U) (v:ℝ) (b:P.Bid) :
    countPayoff P.eta v b (P.actualCountInterim N c F G b)=
      Finishing01Menus.actualRowInterim (N:=N) P.xi P.z P.L P.U c P.categories F G v b := by
  unfold countPayoff actualCountInterim Finishing01Menus.actualRowInterim
  simp only [←FiniteLaw.expect_add,←FiniteLaw.expect_const_mul,←FiniteLaw.expect_sub]
  exact FiniteLaw.expect_congr _ fun kind=> P.patternCountInterim_payoff c kind F G hG v b

lemma actualCountInterim_reconstruct (N c:ℕ) (F G:Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hG:∀ᵐb∂G,b∈ Icc P.L P.U) (b:P.Bid) :
    P.actualCountInterim N c F G b=
      reconstructCountMass P.eta b
        (Finishing01Menus.actualRowInterim (N:=N) P.xi P.z P.L P.U c P.categories F G 0 b)
        (Finishing01Menus.actualRowInterim (N:=N) P.xi P.z P.L P.U c P.categories F G 1 b) := by
  have hh:=reconstructCountMass_eq P.eta b P.eta_pos.ne' (P.bid_pos b).ne'
    (P.actualCountInterim N c F G b) (P.actualCountInterim_total N c F G hG b)
  rw [P.actualCountInterim_payoff N c F G hG 0 b,
    P.actualCountInterim_payoff N c F G hG 1 b] at hh
  exact hh.symm

def originalCountInterim (M c:ℕ) (low:ProbabilityMeasure P.Low)
    (mu:Measure P.Value) [IsProbabilityMeasure mu] (pi:Law (A:=P.Bid) mu)
    (b:P.Bid) (j:Fin 3) : ℝ :=
  P.actualCountInterim (M-1) c (Finishing01Menus.lowReal P low) (P.realBaseLaw mu pi) b j

theorem originalCountInterim_uniform (c:ℕ→ℕ)
    (hc:Tendsto (fun M=>(c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho))
    (low:ℕ→ ProbabilityMeasure P.Low) (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:ℕ→ Law (A:=P.Bid) mu) :
    ∀ eps>0,∀ᶠM in atTop,∀ b:P.Bid,∀ j:Fin 3,
      |P.originalCountInterim M (c M) (low M) mu (pi M) b j-
        limitingCountMass P.z (exposure P.xi (P.price mu (pi M)) b) j|< eps := by
  intro eps heps
  let C:ℝ:=2+(1/P.L+2)/P.eta
  have hC:0< C:=by dsimp [C];have hL:=P.L_pos;have heta:=P.eta_pos;positivity
  obtain ⟨N0,hN0⟩:=Filter.eventually_atTop.mp
    (Finishing01Menus.full_row_reference_limit P P.U P.L_lt_U.le P.box_lower P.box_upper
      c hc 1 (by norm_num) (eps/(2*C)) (by positivity))
  filter_upwards [eventually_ge_atTop (N0+1)] with M hM b j
  have hidx:M-1+1=M:=by omega
  let F:=Finishing01Menus.lowReal P (low M)
  let G:=P.realBaseLaw mu (pi M)
  have hm:=hN0 (M-1) (by omega) P.U ⟨P.L_lt_U.le,le_rfl⟩ F G
    (P.realBaseLaw_box mu (pi M))
  have h0:=hm 0 (by norm_num) b b.property
  have h1:=hm 1 (by norm_num) b b.property
  rw [hidx] at h0 h1
  have hprice:P.h0/reciprocalMean G=P.price mu (pi M) := by
    dsimp only [G]
    rw [P.reciprocal_realBaseLaw]
    rfl
  rw [hprice] at h0 h1
  have hrec:=reconstructCountMass_error P.eta_pos P.L_pos b.property.1
    (show 0≤ eps/(2*C) by positivity) h0.le h1.le j
  rw [←P.actualCountInterim_reconstruct (M-1) (c M) F G
    (P.realBaseLaw_box mu (pi M)) b] at hrec
  have hlim:reconstructCountMass P.eta b
      (P.reference 0 (P.price mu (pi M)) b)
      (P.reference 1 (P.price mu (pi M)) b)=
      limitingCountMass P.z (exposure P.xi (P.price mu (pi M)) b) := by
    unfold reference
    rw [←countPayoff_limit P.eta P.z 0 b _,←countPayoff_limit P.eta P.z 1 b _]
    exact reconstructCountMass_eq P.eta b P.eta_pos.ne' (P.bid_pos b).ne'
      _ (limitingCountMass_total _ _)
  change |P.originalCountInterim M (c M) (low M) mu (pi M) b j-
      reconstructCountMass P.eta b (P.reference 0 (P.price mu (pi M)) b)
        (P.reference 1 (P.price mu (pi M)) b) j|≤ C*(eps/(2*C)) at hrec
  rw [hlim] at hrec
  exact hrec.trans_lt (by field_simp [hC.ne'];linarith)

lemma limitingCountMass_lipschitz {z q r:ℝ} (hz:0≤ z) (hz1:z≤1)
    (hq:q∈ Icc (0:ℝ) 1) (hr:r∈ Icc (0:ℝ) 1) (j:Fin 3) :
    |limitingCountMass z q j-limitingCountMass z r j|≤2*|q-r| := by
  have hb:|binomialTwoMass q j-binomialTwoMass r j|≤2*|q-r| := by
    fin_cases j
    · have he:(1-q)^2-(1-r)^2=(r-q)*(2-q-r):=by ring
      change |(1-q)^2-(1-r)^2| ≤ 2*|q-r|
      rw [he,abs_mul,abs_sub_comm r q]
      have hbound : |2-q-r| ≤ 2 := abs_le.mpr ⟨by linarith [hq.2,hr.2],by linarith [hq.1,hr.1]⟩
      exact (mul_le_mul_of_nonneg_left hbound (abs_nonneg (q-r))).trans_eq (by ring)
    · have he:2*q*(1-q)-2*r*(1-r)=2*(q-r)*(1-q-r):=by ring
      change |2*q*(1-q)-2*r*(1-r)| ≤ 2*|q-r|
      rw [he,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      have hh:=mul_le_mul_of_nonneg_left (show |1-q-r|≤1 from
        abs_le.mpr ⟨by linarith [hq.2,hr.2],by linarith [hq.1,hr.1]⟩)
        (mul_nonneg (by norm_num : (0:ℝ)≤2) (abs_nonneg (q-r)))
      simpa using hh
    · have he:q^2-r^2=(q-r)*(q+r):=by ring
      change |q^2-r^2| ≤ 2*|q-r|
      rw [he,abs_mul]
      have hbound : |q+r| ≤ 2 := abs_le.mpr ⟨by linarith [hq.1,hr.1],by linarith [hq.2,hr.2]⟩
      exact (mul_le_mul_of_nonneg_left hbound (abs_nonneg (q-r))).trans_eq (by ring)
  have he:limitingCountMass z q j-limitingCountMass z r j=
      (1-z)*(binomialTwoMass q j-binomialTwoMass r j):=by unfold limitingCountMass;ring
  rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr hz1)]
  have hm:=mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hz1)
  nlinarith [abs_nonneg (q-r)]

def conditionalCountMass (M c:ℕ) (low:ProbabilityMeasure P.Low)
    (mu:Measure P.Value) [IsProbabilityMeasure mu] (pi:Law (A:=P.Bid) mu)
    (sigma:Kernel P.Value P.Bid) (v:P.Value) (j:Fin 3) : ℝ :=
  ∫b:P.Bid,P.originalCountInterim M c low mu pi b j ∂sigma v

def OriginalConditionalCountLimit (c:ℕ→ℕ) (low:ℕ→ ProbabilityMeasure P.Low)
    (mu:Measure P.Value) [IsProbabilityMeasure mu] (pi:ℕ→ Law (A:=P.Bid) mu)
    (lam:ℝ) : Prop :=
  ∀ sigma:ℕ→ Kernel P.Value P.Bid,
    (∀ M,IsMarkovKernel (sigma M))→
    (∀ M,mu⊗ₘsigma M=((pi M).1:Measure (P.Value×P.Bid)))→
    ∀ᵐv∂mu,∀ j:Fin 3,
      Tendsto (fun M=> P.conditionalCountMass M (c M) (low M) mu (pi M) (sigma M) v j)
        atTop (𝓝 (limitingCountMass P.z (P.qResponse v lam) j))

theorem original_conditional_counts (c:ℕ→ℕ)
    (hc:Tendsto (fun M=>(c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho))
    (low:ℕ→ ProbabilityMeasure P.Low) (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:ℕ→ Law (A:=P.Bid) mu) (hIC:P.EventualActualIC c low mu pi)
    (lam:P.Price) (hprice:Tendsto (fun M=> P.price mu (pi M)) atTop (𝓝 (lam:ℝ))) :
    P.OriginalConditionalCountLimit c low mu pi lam := by
  intro sigma hmark hdis
  letI : ∀ M:ℕ,IsMarkovKernel (sigma M):=hmark
  let f (M:ℕ) (t:P.Value×P.Bid) (j:Fin 3):=
    P.originalCountInterim M (c M) (low M) mu (pi M) t.2 j-
      limitingCountMass P.z (P.qResponse t.1 lam) j
  have hm (M:ℕ) (j:Fin 3):Measurable (fun t:P.Value×P.Bid=> f M t j) := by
    apply Measurable.sub
    · exact (P.measurable_actualCountInterim (M-1) (c M)
        (Finishing01Menus.lowReal P (low M)) (P.realBaseLaw mu (pi M)) j).comp measurable_snd
    · have hq:Measurable (fun t:P.Value×P.Bid=> P.qResponse t.1 lam) :=
        (P.continuous_response.comp (continuous_fst.prodMk continuous_const)).measurable
      unfold limitingCountMass binomialTwoMass pointMass
      split_ifs <;> fun_prop
  have happrox:∀ eps>0,∀ᶠM in atTop,∀ᵐt∂((pi M).1:Measure (P.Value×P.Bid)),∀ j:Fin 3,
      |f M t j|< eps := by
    intro eps heps
    have hmenus:=P.uniform_actual_menus c hc low mu pi
    filter_upwards [P.originalCountInterim_uniform c hc low mu pi (eps/2) (by linarith),
      P.supported_final_exposure c low mu pi hIC hmenus lam hprice (eps/4) (by linarith)]
      with M hC hQ
    filter_upwards [hQ] with t ht j
    have hq:=P.exposure_interior (P.compactPrice mu (pi M)) t.2
    have hr:=(P.qResponse_spec t.1 lam).1
    have hh:=limitingCountMass_lipschitz P.z_nonneg P.z_lt_one.le
      ⟨hq.1.le,hq.2.le⟩ ⟨hr.1.le,hr.2.le⟩ j
    change |limitingCountMass P.z (exposure P.xi (P.price mu (pi M)) t.2) j-
      limitingCountMass P.z (P.qResponse t.1 lam) j| ≤
      2*|exposure P.xi (P.price mu (pi M)) t.2-P.qResponse t.1 lam| at hh
    dsimp only [f]
    exact (abs_sub_le _ (limitingCountMass P.z (exposure P.xi (P.price mu (pi M)) t.2) j) _).trans_lt
      (by linarith [hC t.2 j])
  choose threshold hthreshold using fun n:ℕ=> Filter.eventually_atTop.mp
    (happrox (1/((n:ℝ)+1)) (by positivity))
  have hcommon:∀ᵐv∂mu,∀ n M:ℕ,threshold n≤ M→∀ᵐb∂sigma M v,∀ j:Fin 3,
      |f M (v,b) j|<1/((n:ℝ)+1) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro M
    by_cases hNM:threshold n≤ M
    · have hjoint:=hthreshold n M hNM
      rw [←hdis M] at hjoint
      have hmeas:MeasurableSet {t:P.Value×P.Bid|∀ j:Fin 3,|f M t j|<1/((n:ℝ)+1)} := by
        simp only [setOf_forall]
        exact MeasurableSet.iInter (fun j=> measurableSet_lt (hm M j).abs measurable_const)
      have hh:=(Measure.ae_compProd_iff hmeas).mp hjoint
      exact hh.mono fun v hv _=> hv
    · exact Filter.Eventually.of_forall fun v h=> False.elim (hNM h)
  filter_upwards [hcommon] with v hv j
  rw [Metric.tendsto_nhds]
  intro eps heps
  obtain ⟨n,hn⟩:=exists_nat_one_div_lt heps
  filter_upwards [eventually_ge_atTop (threshold n)] with M hM
  have hbound:=hv n M hM
  have hi:Integrable (fun b:P.Bid=> P.originalCountInterim M (c M) (low M) mu (pi M) b j)
      (sigma M v) :=
    Integrable.of_bound (P.measurable_actualCountInterim (M-1) (c M)
      (Finishing01Menus.lowReal P (low M)) (P.realBaseLaw mu (pi M)) j).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun b=> by
        have hb:=P.actualCountInterim_mem (M-1) (c M)
          (Finishing01Menus.lowReal P (low M)) (P.realBaseLaw mu (pi M))
          (P.realBaseLaw_box mu (pi M)) b j
        change ‖P.actualCountInterim (M-1) (c M) (Finishing01Menus.lowReal P (low M))
          (P.realBaseLaw mu (pi M)) b j‖ ≤ 1
        rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
        exact hb.2)
  have hh:=norm_integral_le_of_norm_le_const (μ:=sigma M v)
    (f:=fun b:P.Bid=> f M (v,b) j) (C:=1/((n:ℝ)+1))
    (hbound.mono fun b hb=> by simpa only [Real.norm_eq_abs] using (hb j).le)
  dsimp only [f] at hh
  rw [integral_sub hi (integrable_const _),integral_const,probReal_univ,one_smul,mul_one] at hh
  simpa only [conditionalCountMass,Real.dist_eq,Real.norm_eq_abs] using hh.trans_lt hn

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
