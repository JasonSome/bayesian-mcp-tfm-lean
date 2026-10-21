import FCAppendix.Affine.Tail04.AllCountActiveFiniteGain
import FCAppendix.Affine.Tail04.OriginalActiveCrossingCarrier
import FCAppendix.Affine.Tail04.NativeFlagTransport

noncomputable section
namespace FCAppendix.Affine.Tail04.IntegratedActiveFiniteGain
open MeasureTheory ProbabilityTheory Set Classical
open AllCountActiveFiniteGain ActiveGainUniformModulus ActualActiveFiniteGain
open EqualPrivateSignal OriginalActiveCrossingCarrier
open scoped BigOperators

theorem finite_common_radius {ι : Type*} [Fintype ι]
    (r : ι→ℝ) (hr : ∀ i,0< r i) : ∃ δ : ℝ,0< δ ∧ ∀ i,δ≤ r i := by
  let S := ∑ i,1/r i
  have hS : 0≤ S := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hr i)).le)
  refine ⟨1/(1+S),by positivity,?_⟩
  intro i
  have hi : 1/r i≤ S := Finset.single_le_sum
    (fun j _ => (one_div_pos.mpr (hr j)).le) (Finset.mem_univ i)
  have hh := one_div_le_one_div_of_le (one_div_pos.mpr (hr i))
    (show 1/r i≤1+S by linarith)
  simpa only [one_div_one_div] using hh

section Measurability
variable {A : ℕ} [Nonempty (Fin A)]

omit [Nonempty (Fin A)] in
lemma measurable_weightFailure (H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ)
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Measurable (fun b : Fin A→ℝ => badWeightProbability
      (ActualFallbackPromotion.effectivePhi lowPresent
        (TypicalGuardStatistics.phi A H0 H1 c ξ B R Rp width reg ν0 ν1)) e0 F b) := by
  apply NativeFlag.measurable_finite_probability
  · intro z
    exact (continuous_iff_continuousAt.mpr (fun b =>
      continuousAt_sourceFlagLaw_mass e0 F b z)).measurable
  · intro z
    apply MeasurableSet.compl
    change MeasurableSet {b : Fin A→ℝ | ∀ target : Fin A,
      targetTypicalWeight (ActualFallbackPromotion.effectivePhi lowPresent
        (TypicalGuardStatistics.phi A H0 H1 c ξ B R Rp width reg ν0 ν1)) b target z=1}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro target
    apply measurableSet_eq_fun _ measurable_const
    cases lowPresent
    · simp only [ActualFallbackPromotion.effectivePhi,Bool.false_eq_true,if_false,targetTypicalWeight]
      exact measurable_const
    · exact (UnequalNoisyCountPayoff.measurable_phi H0 H1 c ξ B R Rp width reg ν0 ν1 _).comp
        (UnequalNoisyCountPayoff.measurable_mixedReciprocalSum _)

omit [Nonempty (Fin A)] in
lemma measurable_freeze {Ω : Type*} [MeasurableSpace Ω]
    (b : Ω→ Fin A→ℝ) (hb : Measurable b) (i : Fin A) (y : Ω→ℝ) (hy : Measurable y) :
    Measurable (fun z => freezeFocal (b z) i (y z)) := by
  apply measurable_pi_lambda
  intro j
  let bi := (measurable_pi_apply i).comp hb
  let bj := (measurable_pi_apply j).comp hb
  exact Measurable.ite ((measurableSet_le bi bj).inter (measurableSet_le bj hy)) bi bj

lemma measurable_physicalUtility (H0 H1 c : ℕ) {ξ B R Rp width e0 F : ℝ}
    (hξ : 0< ξ) (hη0 : 0≤1-2*ξ) (hη1 : 1-2*ξ≤1)
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (σ : ProbabilityMeasure (Signal H0 R Rp)) (i : Fin A) :
    Measurable (fun p : ℝ×(Fin A→ Icc (1:ℝ) B) =>
      physicalUtility H0 H1 c ξ B R Rp width e0 F hη0 hη1 reg lowPresent ν0 ν1 σ p.1 p.2 i) := by
  have hm (r : Fin 3) : Measurable (fun b : Fin A→ Icc (1:ℝ) B =>
      (physicalCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 σ b i).mass r) := by
    by_cases h : H0=H1
    · simp only [physicalCount,if_pos h,EqualPrivateActiveRelabel.countLaw_sorted hξ]
      exact ((EqualPrivateCountPayoff.continuous_countLaw_mass A H0 c R Rp ξ 1 B
        hξ (by norm_num) i r).comp (continuous_id.prodMk continuous_const)).measurable
    · simp only [physicalCount,if_neg h]
      exact (UnequalNoisyCountPayoff.measurable_rawCount_mass H0 H1 c ξ B R Rp width e0 F
        reg lowPresent ν0 ν1 i r).comp
          (measurable_pi_lambda _ (fun j => measurable_subtype_coe.comp (measurable_pi_apply j)))
  unfold physicalUtility affineCountUtility CountLaw.utility FiniteLaw.expect
  apply Finset.measurable_sum
  intro r _
  apply ((hm r).comp measurable_snd).mul
  unfold userPayoff
  exact ((measurable_fst.mul measurable_const).sub
    ((measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_snd)).mul
      measurable_const)).sub measurable_const

end Measurability

attribute [local irreducible] physicalUtility

section Family
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace Ω]
  (a H0 H1 : ι→ℕ) (reg low : ι→ Bool) (c m : ℕ)
  (ξ B R Rp width F : ℝ) (e0 : ι→ℝ)
  (ν0 : ∀ q,FiniteLaw (Marks (H0 q))) (ν1 : ∀ q,FiniteLaw (Marks (H1 q)))
  (σ : ∀ q,ProbabilityMeasure (Signal (H0 q) R Rp))
  (focal : ∀ q,Fin (a q+1)) (tag : Ω→ ι)
  (rows : ∀ q,Ω→ Fin (a q+1)→ Icc (1:ℝ) B)
  (value : Ω→ℝ) (raised : Ω→ Icc (1:ℝ) B)
  (hη0 : 0≤1-2*ξ) (hη1 : 1-2*ξ≤1)

def actualGain (z : Ω) : ℝ :=
  let q := tag z
  physicalUtility (H0 q) (H1 q) c ξ B R Rp width (e0 q) F hη0 hη1
      (reg q) (low q) (ν0 q) (ν1 q) (σ q) (value z)
        (Function.update (rows q z) (focal q) (raised z)) (focal q)-
    physicalUtility (H0 q) (H1 q) c ξ B R Rp width (e0 q) F hη0 hη1
      (reg q) (low q) (ν0 q) (ν1 q) (σ q) (value z) (rows q z) (focal q)

def actualBeta (z : Ω) : ℝ :=
  let q := tag z
  let b := fun j => (rows q z j:ℝ)
  let phi := ActualFallbackPromotion.effectivePhi (low q)
    (TypicalGuardStatistics.phi (a q+1) (H0 q) (H1 q) c ξ B R Rp width (reg q) (ν0 q) (ν1 q))
  badWeightProbability phi (e0 q) F (freezeFocal b (focal q) (raised z))+
    badWeightProbability phi (e0 q) F (Function.update b (focal q) (raised z))

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in
lemma actualBeta_bounds (z : Ω) :
    actualBeta a H0 H1 reg low c ξ B R Rp width F e0 ν0 ν1 focal tag rows raised z∈Icc (0:ℝ) 2 := by
  dsimp only [actualBeta]
  constructor
  · exact add_nonneg (FiniteLaw.prob_nonneg _ _) (FiniteLaw.prob_nonneg _ _)
  · calc
      _ ≤ 1+1 := add_le_add (FiniteLaw.prob_le_one _ _) (FiniteLaw.prob_le_one _ _)
      _ = 2 := by norm_num

lemma measurable_actualBeta (htag : Measurable tag) (hrows : ∀ q,Measurable (rows q))
    (hraised : Measurable raised) :
    Measurable (actualBeta a H0 H1 reg low c ξ B R Rp width F e0 ν0 ν1 focal tag rows raised) := by
  let g (z : Ω) (q : ι) : ℝ :=
    let b := fun j => (rows q z j:ℝ)
    let phi := ActualFallbackPromotion.effectivePhi (low q)
      (TypicalGuardStatistics.phi (a q+1) (H0 q) (H1 q) c ξ B R Rp width (reg q) (ν0 q) (ν1 q))
    badWeightProbability phi (e0 q) F (freezeFocal b (focal q) (raised z))+
      badWeightProbability phi (e0 q) F (Function.update b (focal q) (raised z))
  change Measurable (fun z => g z (tag z))
  apply LocalCoordinates.measurable_finite_eval tag g htag
  intro q
  have hb : Measurable (fun z j => (rows q z j:ℝ)) :=
    measurable_pi_lambda _ (fun j => measurable_subtype_coe.comp
      ((measurable_pi_apply j).comp (hrows q)))
  have hy := measurable_subtype_coe.comp hraised
  have hf := measurable_weightFailure (A:=a q+1) (H0 q) (H1 q) c ξ B R Rp width (e0 q) F
    (reg q) (low q) (ν0 q) (ν1 q)
  exact (hf.comp (measurable_freeze _ hb (focal q) _ hy)).add
    (hf.comp (Resample.measurable_update_pair (focal q) |>.comp (hy.prodMk hb)))

lemma measurable_actualGain (hξ : 0< ξ) (htag : Measurable tag) (hrows : ∀ q,Measurable (rows q))
    (hvalue : Measurable value) (hraised : Measurable raised) :
    Measurable (actualGain a H0 H1 reg low c ξ B R Rp width F e0 ν0 ν1 σ focal tag rows
      value raised hη0 hη1) := by
  let g (z : Ω) (q : ι) : ℝ :=
    physicalUtility (H0 q) (H1 q) c ξ B R Rp width (e0 q) F hη0 hη1
      (reg q) (low q) (ν0 q) (ν1 q) (σ q) (value z)
        (Function.update (rows q z) (focal q) (raised z)) (focal q)-
    physicalUtility (H0 q) (H1 q) c ξ B R Rp width (e0 q) F hη0 hη1
      (reg q) (low q) (ν0 q) (ν1 q) (σ q) (value z) (rows q z) (focal q)
  change Measurable (fun z => g z (tag z))
  apply LocalCoordinates.measurable_finite_eval tag g htag
  intro q
  have hu := measurable_physicalUtility (B:=B) (width:=width) (e0:=e0 q) (F:=F)
    (H0 q) (H1 q) c hξ hη0 hη1
    (reg q) (low q) (ν0 q) (ν1 q) (σ q) (focal q)
  exact (hu.comp (hvalue.prodMk
    (Resample.measurable_update_pair (focal q) |>.comp (hraised.prodMk (hrows q))))).sub
      (hu.comp (hvalue.prodMk (hrows q)))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem exists_family_radius {C vhi : ℝ}
    (hcard : ∀ q,a q+1≤ m) (hξ : 0< ξ) (hξh : ξ≤1/2) (hw : 0< width)
    (he0 : ∀ q,0≤ e0 q) (he1 : ∀ q,e0 q≤1) (hF : 1< F) (hCF : C≤ F)
    (hC : 1≤ C) (hvhi : 0≤ vhi) {e : ℝ} (he : 0< e) :
    ∃ δ : ℝ,0< δ ∧ ∀ q,∀ B∈Icc (1:ℝ) C,∀ Rp∈Icc (0:ℝ) 1,
      ∀ v∈Icc (0:ℝ) vhi,(1-ξ)*B<1 → ∀ τ : ProbabilityMeasure (Signal (H0 q) R Rp),
      ∀ b : Fin (a q+1)→ Icc (1:ℝ) B,
      (∀ j k,j≠k → (b j:ℝ)≠(b k:ℝ)) → (b (focal q):ℝ)≤ v →
      ∀ y : Icc (1:ℝ) B,(b (focal q):ℝ)< y → (y:ℝ)-(b (focal q):ℝ)< δ →
      populationCoefficient m ξ width (e0 q) F C*
          (if H0 q=H1 q then 0 else AtypicalFittingFiniteLoss.crossingCount
            (fun j => (b j:ℝ)) (focal q) y)-
        (vhi+2*C+1)*
          (badWeightProbability (ActualFallbackPromotion.effectivePhi (low q)
              (TypicalGuardStatistics.phi (a q+1) (H0 q) (H1 q) c ξ B R Rp width (reg q) (ν0 q) (ν1 q)))
            (e0 q) F (freezeFocal (fun j => (b j:ℝ)) (focal q) y)+
          badWeightProbability (ActualFallbackPromotion.effectivePhi (low q)
              (TypicalGuardStatistics.phi (a q+1) (H0 q) (H1 q) c ξ B R Rp width (reg q) (ν0 q) (ν1 q)))
            (e0 q) F (Function.update (fun j => (b j:ℝ)) (focal q) (y:ℝ)))*
          AtypicalFittingFiniteLoss.crossingCount (fun j => (b j:ℝ)) (focal q) y-
        2*e-smoothCoefficient ξ C vhi*((y:ℝ)-(b (focal q):ℝ))≤
      physicalUtility (H0 q) (H1 q) c ξ B R Rp width (e0 q) F (by linarith) (by linarith)
        (reg q) (low q) (ν0 q) (ν1 q) τ v (Function.update b (focal q) y) (focal q)-
      physicalUtility (H0 q) (H1 q) c ξ B R Rp width (e0 q) F (by linarith) (by linarith)
        (reg q) (low q) (ν0 q) (ν1 q) τ v b (focal q) := by
  have hex (q : ι) := AllCountActiveFiniteGain.exists_finite_gain_radius
    (R:=R) (vlo:=0)
    (H0 q) (H1 q) c m (hcard q) hξ hξh hw (he0 q) (he1 q) hF hCF hC hvhi
      (reg q) (low q) (ν0 q) (ν1 q) (focal q) he
  choose r hr hp using hex
  obtain ⟨δ,hδ,hδr⟩ := finite_common_radius r hr
  refine ⟨δ,hδ,?_⟩
  intro q B hB Rp hRp v hv hsep τ b hno hval y hy hsmall
  exact hp q B hB Rp hRp v hv hsep τ b hno hval y hy (hsmall.trans_le (hδr q))

end Family

section Integration
variable {X : Type*} [MeasurableSpace X] {N : ℕ}

theorem integrate_cluster_gain (μ : Measure X) [IsProbabilityMeasure μ]
    (E F active : Set X) (hE : MeasurableSet E) (hF : MeasurableSet F) (ha : MeasurableSet active)
    (bid raised : X→ℝ) (hb : Measurable bid) (hr : Measurable raised)
    (hEa : E⊆active) (hordered : ∀ x∈E,∀ y∈E,bid y≤ raised x)
    (hlocal : ∀ x∈E,∀ y,crossing active bid raised x y → y∈F)
    (equal : X×(Fin (N+1)→ X)→ Prop) (hequal : MeasurableSet {z | equal z})
    (β gain : X×(Fin (N+1)→ X)→ℝ) (hβ : Measurable β) (hgain : Measurable gain)
    (hβbound : ∀ z,β z∈Icc (0:ℝ) 2)
    (gainBound : ℝ) (hgainBound : ∀ᵐ z ∂(μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ)),
      ‖gain z‖≤ gainBound)
    {A K err εeq εbad : ℝ} (hA : 0≤ A) (hK : 0≤ K)
    (hpoint : ∀ᵐ z ∂(μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ)),
      A*(if equal z then 0 else crossingCount active bid raised z)-
        K*β z*crossingCount active bid raised z-err≤ gain z)
    (heqConditional : ∀ j,∀ x∈E,∀ y∈E,
      (Measure.pi (fun _ : Fin N => μ)).real {r | equal (x,restore j y r)}≤ εeq)
    (hbadConditional : ∀ j,∀ x∈E,∀ y∈F,
      (∫ r,β (x,restore j y r) ∂Measure.pi (fun _ : Fin N => μ))≤ εbad)
    (hIC : (∫ z,gain z ∂(μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ)))≤0) :
    A*(N+1:ℕ)*(1/2-εeq)*(μ.real E)^2≤
      K*(N+1:ℕ)*εbad*μ.real E*μ.real F+err*μ.real E := by
  let ν := (μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ))
  let term (j : Fin (N+1)) (z : X×(Fin (N+1)→ X)) : ℝ :=
    if crossing active bid raised z.1 (z.2 j) then 1 else 0
  have ht (j : Fin (N+1)) : Measurable (term j) :=
    Measurable.ite ((measurableSet_crossing active ha bid raised hb hr).preimage
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))) measurable_const measurable_const
  have htb (j : Fin (N+1)) (z) : term j z∈Icc (0:ℝ) 1 := by
    dsimp [term];split_ifs <;> constructor <;> norm_num
  have htloc (j : Fin (N+1)) (x : X) (hx : x∈E) (r) (hy : r j∉F) : term j (x,r)=0 := by
    exact if_neg (fun h => hy (hlocal x hx (r j) h))
  have hloss := sum_localized_error μ E F hE hF term ht htb htloc β hβ 2 (by norm_num)
    hβbound εbad hbadConditional
  change (∫ z,crossingCount active bid raised z*β z ∂ν)≤_ at hloss
  have hord := orderedCount_without_equal_lower μ E hE bid hb equal hequal εeq heqConditional
  have hmCross := measurable_crossingCount (N:=N) active ha bid raised hb hr
  have hmOrd := measurable_orderedCount (N:=N) E hE bid hb
  have hiCross := integrable_crossingCount (N:=N) μ E active ha bid raised hb hr
  have hiOrd := integrable_orderedCount (N:=N) μ E hE bid hb
  have hiLoss : Integrable (fun z => crossingCount active bid raised z*β z) ν := by
    apply Integrable.of_bound (hmCross.mul hβ).aestronglyMeasurable (2*(N+1:ℕ))
    exact ae_of_all _ fun z => by
      have hcross := crossingCount_bounds (N:=N) active bid raised z
      change ‖crossingCount active bid raised z*β z‖≤_
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hcross.1 (hβbound z).1)]
      nlinarith only [hcross.1,hcross.2,(hβbound z).1,(hβbound z).2]
  have hiPos : Integrable (fun z => if equal z then (0:ℝ) else orderedCount E bid z) ν :=
    Integrable.of_bound (Measurable.ite hequal measurable_const hmOrd).aestronglyMeasurable
      (N+1:ℕ) (ae_of_all _ fun z => by
        split_ifs
        · rw [norm_zero]
          positivity
        · rw [Real.norm_eq_abs,abs_of_nonneg (orderedCount_bounds E bid z).1]
          exact (orderedCount_bounds E bid z).2)
  have hiG : Integrable gain ν := Integrable.of_bound hgain.aestronglyMeasurable gainBound hgainBound
  have hc : ∀ᵐ z ∂ν,orderedCount E bid z≤ crossingCount active bid raised z := by
    have hx : ∀ᵐ z ∂ν,z.1∈E :=
      (measurePreserving_fst (μ:=μ.restrict E) (ν:=Measure.pi (fun _ : Fin (N+1) => μ))).quasiMeasurePreserving.ae
        (ae_restrict_mem hE)
    filter_upwards [hx] with z hz
    apply Finset.sum_le_sum
    intro j _
    dsimp [orderedCoordinate]
    by_cases hj : z.2 j∈E ∧ bid z.1≤ bid (z.2 j)
    · have hcr : crossing active bid raised z.1 (z.2 j) :=
        ⟨hEa hj.1,hj.2,hordered z.1 hz (z.2 j) hj.1⟩
      simp only [if_pos hj,if_pos hcr]
      exact le_rfl
    · simp only [if_neg hj]
      split_ifs <;> norm_num
  have hiL := ((hiPos.const_mul A).sub (hiLoss.const_mul K)).sub (integrable_const err)
  have hmono := integral_mono_ae hiL hiG (by
    filter_upwards [hpoint,hc] with z hp hc
    have hp' : (if equal z then (0:ℝ) else orderedCount E bid z)≤
        (if equal z then 0 else crossingCount active bid raised z) := by
      by_cases he : equal z
      · simp only [if_pos he,le_refl]
      · simpa only [if_neg he] using hc
    have hs := mul_le_mul_of_nonneg_left hp' hA
    change A*(if equal z then (0:ℝ) else orderedCount E bid z)-
      K*(crossingCount active bid raised z*β z)-err≤gain z
    nlinarith only [hp,hs])
  change (∫ z,A*(if equal z then (0:ℝ) else orderedCount E bid z)-
    K*(crossingCount active bid raised z*β z)-err ∂ν)≤∫ z,gain z ∂ν at hmono
  have hexpand0 :
      (∫ z,A*(if equal z then (0:ℝ) else orderedCount E bid z)-
        K*(crossingCount active bid raised z*β z)-err ∂ν)=
      (∫ z,A*(if equal z then (0:ℝ) else orderedCount E bid z)-
        K*(crossingCount active bid raised z*β z) ∂ν)-(∫ _z,err ∂ν) := by
    simpa only [Pi.sub_apply] using
      integral_sub ((hiPos.const_mul A).sub (hiLoss.const_mul K)) (integrable_const err)
  have hexpand1 :
      (∫ z,A*(if equal z then (0:ℝ) else orderedCount E bid z)-
        K*(crossingCount active bid raised z*β z) ∂ν)=
      (∫ z,A*(if equal z then (0:ℝ) else orderedCount E bid z) ∂ν)-
        (∫ z,K*(crossingCount active bid raised z*β z) ∂ν) := by
    simpa only [Pi.sub_apply] using integral_sub (hiPos.const_mul A) (hiLoss.const_mul K)
  rw [hexpand0,hexpand1,integral_const_mul,integral_const_mul,integral_const] at hmono
  have hmass : ν.real univ=μ.real E := by
    simp only [ν,measureReal_def,←univ_prod_univ,Measure.prod_prod,measure_univ,mul_one,
      Measure.restrict_apply_univ]
  rw [hmass,smul_eq_mul] at hmono
  have hp := mul_le_mul_of_nonneg_left hord hA
  have hl := mul_le_mul_of_nonneg_left hloss hK
  dsimp only [ν] at hmono hloss hp hl
  nlinarith only [hmono,hIC,hp,hl]

end Integration
end FCAppendix.Affine.Tail04.IntegratedActiveFiniteGain
