import FCAppendix.Affine.Tail04.NativePartialReports

noncomputable section
namespace FCAppendix.Affine.Tail04.NativePartialDeviation
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativePartialReports
open scoped BigOperators

variable {m c : ℕ} (D : Data m c) (Γ : FiniteGame m 2 c Seed)

def badMass (i : Fin m) : ℝ :=
  (backgroundLaw Γ).real {ω | ¬goodBackground D i ω}

lemma badMass_nonneg (i : Fin m) : 0≤ badMass D Γ i := measureReal_nonneg

def actualRegimeLaw (i : Fin m) : FiniteLaw Bool :=
  FiniteLaw.ofMeasure (backgroundLaw Γ) (backgroundRegime D i) (measurable_backgroundRegime D i)

def serviceProb (i : Fin m) : ℝ := (actualRegimeLaw D Γ i).mass false

lemma serviceProb_bounds (i : Fin m) : serviceProb D Γ i∈Icc (0:ℝ) 1 := by
  refine ⟨(actualRegimeLaw D Γ i).nonneg false,?_⟩
  have hu := Finset.single_le_sum (fun r _ => (actualRegimeLaw D Γ i).nonneg r)
    (Finset.mem_univ false)
  exact hu.trans_eq (actualRegimeLaw D Γ i).total

def referenceLaw (i : Fin m) (k : Fin 3) : CountLaw 2 :=
  (actualRegimeLaw D Γ i).map (fun reg => if reg then 0 else k)

lemma referenceLaw_expect (i : Fin m) (k : Fin 3) (f : Fin 3 → ℝ) :
    (referenceLaw D Γ i k).expect f=
      serviceProb D Γ i*f k+(1-serviceProb D Γ i)*f 0 := by
  let ν := actualRegimeLaw D Γ i
  have hb : (Finset.univ : Finset Bool)={false,true} := by decide
  have ht : ν.mass false+ν.mass true=1 := by
    have h := ν.total
    simpa only [hb,Finset.sum_insert (by decide : false∉({true}:Finset Bool)),
      Finset.sum_singleton] using h
  rw [referenceLaw,FiniteLaw.expect_map]
  simp only [FiniteLaw.expect,hb,Finset.sum_insert (by decide : false∉({true}:Finset Bool)),
    Finset.sum_singleton,Bool.false_eq_true,ite_false,ite_true]
  change ν.mass false*f k+ν.mass true*f 0=_
  dsimp only [serviceProb]
  rw [show ν.mass true=1-ν.mass false by linarith]

lemma referenceLaw_mass (i : Fin m) (k r : Fin 3) :
    (referenceLaw D Γ i k).mass r=
      serviceProb D Γ i*(if k=r then 1 else 0)+
        (1-serviceProb D Γ i)*(if (0:Fin 3)=r then 1 else 0) := by
  have h := referenceLaw_expect D Γ i k (fun q => if q=r then (1:ℝ) else 0)
  simpa [FiniteLaw.expect] using h

private lemma integrable_count_function {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → Fin 3) (hf : Measurable f)
    (g : Fin 3 → ℝ) : Integrable (fun ω => g (f ω)) μ :=
  CountLaw.integrable_comp μ f hf g

lemma reference_integral (i : Fin m) (k : Fin 3) (f : Fin 3 → ℝ) :
    (referenceLaw D Γ i k).expect f=
      ∫ ω : Sample m 2 Seed,f (if backgroundRegime D i ω.1 then 0 else k) ∂sampleLaw Γ := by
  rw [referenceLaw,FiniteLaw.expect_map,actualRegimeLaw,FiniteLaw.expect_ofMeasure]
  have hc : Measurable (fun ω : Sample m 2 Seed =>
      if backgroundRegime D i ω.1 then (0:Fin 3) else k) :=
    (measurable_of_countable (fun reg : Bool => if reg then (0:Fin 3) else k)).comp
      ((measurable_backgroundRegime D i).comp measurable_fst)
  have hi := integrable_count_function (sampleLaw Γ) _ hc f
  symm
  rw [sampleLaw,integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => by
    have hh := integral_const (μ:=permLaw 2) (f (if backgroundRegime D i ω then 0 else k))
    simp only [probReal_univ,one_smul] at hh
    convert! hh using 1)

lemma bad_indicator_integral (i : Fin m) :
    (∫ ω : Sample m 2 Seed,if ¬goodBackground D i ω.1 then (1:ℝ) else 0 ∂sampleLaw Γ)=
      badMass D Γ i := by
  have hbad := (measurableSet_goodBackground D i).compl
  have hm : Measurable (fun ω : Sample m 2 Seed =>
      if ¬goodBackground D i ω.1 then (1:ℝ) else 0) :=
    Measurable.ite (hbad.preimage measurable_fst) measurable_const measurable_const
  have hi : Integrable (fun ω : Sample m 2 Seed =>
      if ¬goodBackground D i ω.1 then (1:ℝ) else 0) (sampleLaw Γ) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ (fun ω => by split_ifs <;> norm_num))
  rw [sampleLaw,integral_prod _ hi]
  have he (ω : Background m 2 Seed) :
      (∫ _ : Equiv.Perm (Fin 2),if ¬goodBackground D i ω then (1:ℝ) else 0 ∂permLaw 2)=
        (if ¬goodBackground D i ω then (1:ℝ) else 0) := by
    have hh := integral_const (μ:=permLaw 2) (if ¬goodBackground D i ω then (1:ℝ) else 0)
    simp only [probReal_univ,one_smul] at hh
    convert! hh using 1
  rw [integral_congr_ae (ae_of_all _ he)]
  convert! integral_indicator_one (μ:=backgroundLaw Γ) hbad using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => by
    by_cases hg : goodBackground D i ω <;> simp [Set.indicator,hg])

variable (hpolicy : ∀ j,Γ.policy j=D.completedPolicy j)

include hpolicy in
theorem expect_error (i : Fin m) (price : Icc D.E.R D.E.Rp) (k : Fin 3)
    (f : Fin 3 → ℝ) (C : ℝ) (_hC : 0≤ C) (hosc : ∀ r s,|f r-f s|≤ C) :
    |((problem Γ i).outcome (RawRoutes.action price
        ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) k)).expect f-
      (referenceLaw D Γ i k).expect f|≤ C*badMass D Γ i := by
  let a := RawRoutes.action price ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) k
  let X : Sample m 2 Seed → Fin 3 := focalCount Γ i a
  let Y : Sample m 2 Seed → Fin 3 := fun ω => if backgroundRegime D i ω.1 then 0 else k
  have hX : Measurable X := measurable_focalCount Γ i a
  have hY : Measurable Y :=
    (measurable_of_countable (fun reg : Bool => if reg then (0:Fin 3) else k)).comp
      ((measurable_backgroundRegime D i).comp measurable_fst)
  have hXi := integrable_count_function (sampleLaw Γ) X hX f
  have hYi := integrable_count_function (sampleLaw Γ) Y hY f
  have hbad : Measurable (fun ω : Sample m 2 Seed => if ¬goodBackground D i ω.1 then (1:ℝ) else 0) :=
    Measurable.ite ((measurableSet_goodBackground D i).compl.preimage measurable_fst)
      measurable_const measurable_const
  have hBi : Integrable (fun ω : Sample m 2 Seed => if ¬goodBackground D i ω.1 then (1:ℝ) else 0)
      (sampleLaw Γ) := Integrable.of_bound hbad.aestronglyMeasurable 1
        (ae_of_all _ (fun ω => by split_ifs <;> norm_num))
  rw [problem_outcome,CountLaw.expect_ofMeasure,reference_integral,
    ←integral_sub hXi hYi]
  calc
    |∫ ω : Sample m 2 Seed,f (X ω)-f (Y ω) ∂sampleLaw Γ|≤
        ∫ ω : Sample m 2 Seed,|f (X ω)-f (Y ω)| ∂sampleLaw Γ := abs_integral_le_integral_abs
    _≤∫ ω : Sample m 2 Seed,C*(if ¬goodBackground D i ω.1 then (1:ℝ) else 0) ∂sampleLaw Γ := by
      apply integral_mono_ae (hXi.sub hYi).abs (hBi.const_mul C)
      exact ae_of_all _ (fun ω => by
        change |f (X ω)-f (Y ω)|≤C*(if ¬goodBackground D i ω.1 then (1:ℝ) else 0)
        by_cases hg : goodBackground D i ω.1
        · have he : X ω=Y ω := focalCount_on_good D Γ hpolicy i ω hg price k
          simp only [he,sub_self,abs_zero,hg,not_true_eq_false,ite_false,mul_zero]
          exact le_rfl
        · simpa only [hg,not_false_eq_true,ite_true,mul_one] using hosc (X ω) (Y ω))
    _=C*badMass D Γ i := by rw [integral_const_mul,bad_indicator_integral]

include hpolicy in
theorem mass_error (i : Fin m) (price : Icc D.E.R D.E.Rp) (k r : Fin 3) :
    |((problem Γ i).outcome (RawRoutes.action price
        ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) k)).mass r-
      (referenceLaw D Γ i k).mass r|≤ badMass D Γ i := by
  have h := expect_error D Γ hpolicy i price k (fun s => if s=r then (1:ℝ) else 0)
    1 (by norm_num) (fun s t => by split_ifs <;> norm_num)
  simpa [FiniteLaw.expect] using h

include hpolicy in
theorem success_error (i : Fin m) (price : Icc D.E.R D.E.Rp) (k : Fin 3) (hk : k≠0) :
    |((problem Γ i).outcome (RawRoutes.action price
        ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) k)).success-
      serviceProb D Γ i|≤ badMass D Γ i := by
  have h := mass_error D Γ hpolicy i price k 0
  rw [referenceLaw_mass,if_neg hk,if_pos rfl,mul_zero,zero_add,mul_one,
    (Counts.count_masses _).1] at h
  convert! h using 1
  rw [show (1-((problem Γ i).outcome (RawRoutes.action price
      ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) k)).success)-
      (1-serviceProb D Γ i)=-( ((problem Γ i).outcome (RawRoutes.action price
      ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) k)).success-serviceProb D Γ i) by ring,
    abs_neg]

include hpolicy in
theorem broadcast_duplicates_error (i : Fin m) (price : Icc D.E.R D.E.Rp) :
    |((problem Γ i).outcome (RawRoutes.action price
        ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) 2)).duplicates-
      serviceProb D Γ i|≤ badMass D Γ i := by
  have h := mass_error D Γ hpolicy i price 2 2
  have hr := referenceLaw_mass D Γ i 2 2
  simp only [ite_true,mul_one,show (0:Fin 3)≠2 by decide,ite_false,mul_zero,add_zero] at hr
  rw [hr,(Counts.count_masses _).2.2] at h
  exact h

variable (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hg : Γ.g=0)

include hpolicy hη0 hη1 hA hg in
theorem broadcast_minus_singleton_le (i : Fin m) (price : Icc D.E.R D.E.Rp) (v : ℝ) :
    (problem Γ i).payoff v (RawRoutes.action price
        ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) 2)-
      (problem Γ i).payoff v (RawRoutes.action price
        ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) 1) ≤
      -η*(price:ℝ)*serviceProb D Γ i+
        (2*|v-(price:ℝ)|+η*(price:ℝ))*badMass D Γ i := by
  let hb : 0≤(price:ℝ) := (D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1
  let K1 := (problem Γ i).outcome (RawRoutes.action price hb 1)
  let K2 := (problem Γ i).outcome (RawRoutes.action price hb 2)
  let q := serviceProb D Γ i
  let ε := badMass D Γ i
  have h1 : |K1.success-q|≤ ε := success_error D Γ hpolicy i price 1 (by decide)
  have h2 : |K2.success-q|≤ ε := success_error D Γ hpolicy i price 2 (by decide)
  have hd : |K2.duplicates-q|≤ ε := broadcast_duplicates_error D Γ hpolicy i price
  have hD1 : K1.duplicates=0 := (RawRoutes.singleton_statistics Γ i price hb).2
  have hs : |K2.success-K1.success|≤2*ε := by
    calc
      _=|(K2.success-q)-(K1.success-q)| := by congr 1;ring
      _≤|K2.success-q|+|K1.success-q| := abs_sub _ _
      _≤2*ε := by linarith
  have hterm : (v-(price:ℝ))*(K2.success-K1.success)≤|v-(price:ℝ)| *(2*ε) :=
    (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_left hs (abs_nonneg _))
  have hdup : -η*(price:ℝ)*(K2.duplicates-q)≤ η*(price:ℝ)*ε := by
    have hlo := (abs_le.mp hd).1
    nlinarith [mul_le_mul_of_nonneg_left hlo (mul_nonneg hη0 hb)]
  rw [LowBody.native_affine_zero_fee_payoff Γ hη0 hη1 hA hg,
    LowBody.native_affine_zero_fee_payoff Γ hη0 hη1 hA hg]
  change (v-(price:ℝ))*K2.success-η*(price:ℝ)*K2.duplicates-
    ((v-(price:ℝ))*K1.success-η*(price:ℝ)*K1.duplicates)≤_
  rw [hD1]
  nlinarith only [hterm,hdup]

include hpolicy hη0 hη1 hA hg in
theorem broadcast_strictly_worse (i : Fin m) (price : Icc D.E.R D.E.Rp) (v : ℝ)
    (hmargin : (2*|v-(price:ℝ)|+η*(price:ℝ))*badMass D Γ i<
      η*(price:ℝ)*serviceProb D Γ i) :
    (problem Γ i).payoff v (RawRoutes.action price
      ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) 2)<
    (problem Γ i).payoff v (RawRoutes.action price
      ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans price.2.1) 1) := by
  have h := broadcast_minus_singleton_le D Γ hpolicy η hη0 hη1 hA hg i price v
  linarith

end FCAppendix.Affine.Tail04.NativePartialDeviation
