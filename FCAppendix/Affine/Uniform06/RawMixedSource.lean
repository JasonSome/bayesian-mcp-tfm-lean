import FCAppendix.Affine.Uniform06.MixedLaw
import FCAppendix.Affine.Uniform06.RivalGood

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.RawMixedSource

open MeasureTheory ProbabilityTheory Set LowBody
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.Uniform07
open scoped BigOperators

def demand (ξ b : ℝ) (r : RowRival) : ℝ :=
  if r.1=0 then exposure ξ b r.2 else if r.1=1 then 1 else 1/2

def sign (r : RowRival) : ℝ := if r.1=2 then 1 else if r.1=3 then -1 else 0

def point (ξ b : ℝ) (r : RowRival) : MixedLaw.Pair := (demand ξ b r,sign r)

def source (i : Row) (G : Measure (ℝ × ℝ)) : Measure RowRival :=
  rivalLaw (cutoff i) 0 (1-cutoff i) (G.map Prod.snd)

instance source_probability (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] :
    IsProbabilityMeasure (source i G) := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact rivalLaw_isProbability _ _ _ (cutoff_pos i).le le_rfl
    (sub_nonneg.mpr (cutoff_lt_one i).le) (by ring) _

theorem measurable_demand (ξ b : ℝ) : Measurable (demand ξ b) := by
  unfold demand
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
  · unfold exposure
    fun_prop
  · exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
      measurable_const measurable_const

theorem measurable_sign : Measurable sign := by
  unfold sign
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    measurable_const (Measurable.ite
      (measurableSet_eq_fun measurable_fst measurable_const) measurable_const measurable_const)

theorem measurable_point (ξ b : ℝ) : Measurable (point ξ b) :=
  (measurable_demand ξ b).prodMk measurable_sign

theorem demand_bounds {ξ b : ℝ} (hξ : 0 < ξ) (hb : 0 < b) (r : RowRival) :
    demand ξ b r ∈ Icc (0:ℝ) 1 := by
  unfold demand
  split_ifs
  · exact ⟨exposure_nonneg hξ hb,exposure_le_one _ _ _⟩
  · norm_num
  · norm_num

theorem sign_bounds (r : RowRival) : |sign r| ≤ 1 := by
  unfold sign
  split_ifs <;> norm_num

theorem sign_values (r : RowRival) : sign r=-1 ∨ sign r=0 ∨ sign r=1 := by
  unfold sign
  split_ifs <;> simp

theorem map_source (i : Row) (G : Measure (ℝ × ℝ)) {b : ℝ} (hb : 0 < b) :
    (source i G).map (point (xi i) b)=MixedLaw.law i (MixedLaw.physicalLowerLaw i b G) := by
  let f := point (xi i) b
  have hf : Measurable f := measurable_point _ _
  have hlow : Measurable (fun r : ℝ => ((0:Fin 4),r)) := measurable_const.prodMk measurable_id
  have he : (f ∘ fun r : ℝ => ((0:Fin 4),r))=fun r => (exposure (xi i) b r,0) := by
    funext r
    norm_num [f,point,demand,sign,Fin.ext_iff]
  have hphys : (G.map Prod.snd).map (fun r => (exposure (xi i) b r,0))=
      MixedLaw.lowerLift (MixedLaw.physicalLowerLaw i b G) := by
    rw [MixedLaw.lowerLift,MixedLaw.physicalLowerLaw]
    change (G.map Prod.snd).map (fun r => (exposure (xi i) b r,0)) =
      (G.map (exposure (xi i) b ∘ Prod.snd)).map (fun x : ℝ => (x,(0:ℝ)))
    rw [Measure.map_map (by unfold exposure; fun_prop) measurable_snd,
      Measure.map_map (show Measurable (fun x : ℝ => (x,(0:ℝ))) by fun_prop)
        ((continuous_exposure (xi_pos i) hb).measurable.comp measurable_snd)]
    rfl
  unfold source rivalLaw
  rw [Measure.map_add _ _ hf,Measure.map_add _ _ hf,Measure.map_add _ _ hf,
    Measure.map_smul,Measure.map_smul,Measure.map_smul,Measure.map_smul,
    Measure.map_map hf hlow,he,hphys]
  simp only [ENNReal.ofReal_zero,zero_smul,add_zero,
    Measure.map_dirac' hf]
  change ENNReal.ofReal (cutoff i) • MixedLaw.lowerLift (MixedLaw.physicalLowerLaw i b G)+
      ENNReal.ofReal ((1-cutoff i)/2) • Measure.dirac (f (2,0))+
      ENNReal.ofReal ((1-cutoff i)/2) • Measure.dirac (f (3,0))=_
  have h2 : f (2,0)=((1/2:ℝ),1) := by norm_num [f,point,demand,sign,Fin.ext_iff]
  have h3 : f (3,0)=((1/2:ℝ),-1) := by norm_num [f,point,demand,sign,Fin.ext_iff]
  rw [h2,h3,MixedLaw.law,MixedLaw.upperSignLaw,smul_add,smul_smul,smul_smul,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr (cutoff_lt_one i).le),
    show (1-cutoff i)*(1/2:ℝ)=(1-cutoff i)/2 by ring]
  abel

theorem point_preserving (i : Row) (G : Measure (ℝ × ℝ)) {b : ℝ} (hb : 0 < b) :
    MeasurePreserving (point (xi i) b) (source i G)
      (MixedLaw.law i (MixedLaw.physicalLowerLaw i b G)) :=
  ⟨measurable_point _ _,map_source i G hb⟩

theorem iid_map_source (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] {b : ℝ} (hb : 0 < b) (N : ℕ) :
    (Measure.pi (fun _ : Fin N => source i G)).map
      (fun ω j => point (xi i) b (ω j))=
      Measure.pi (fun _ : Fin N => MixedLaw.law i (MixedLaw.physicalLowerLaw i b G)) := by
  letI : IsProbabilityMeasure ((source i G).map (point (xi i) b)) :=
    Measure.isProbabilityMeasure_map (measurable_point (xi i) b).aemeasurable
  rw [Measure.pi_map_pi (fun _ => (measurable_point (xi i) b).aemeasurable)]
  simp only [map_source i G hb]

theorem integral_source_test (i : Row) (G : Measure (ℝ × ℝ)) {b : ℝ} (hb : 0 < b)
    (F : MixedLaw.Pair → ℝ) (hF : Measurable F) :
    (∫ r, F (point (xi i) b r) ∂source i G)=
      ∫ p, F p ∂MixedLaw.law i (MixedLaw.physicalLowerLaw i b G) := by
  rw [← map_source i G hb, integral_map (measurable_point _ _).aemeasurable hF.aestronglyMeasurable]

theorem sign_mean (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) : (∫ r, sign r ∂source i G)=0 := by
  letI := MixedLaw.physicalLowerLaw_probability i hb G
  have hh := integral_source_test i G hb Prod.snd measurable_snd
  change (∫ r, sign r ∂source i G)=_ at hh
  rw [hh,MixedLaw.sign_mean i _ (MixedLaw.physicalLowerLaw_bounds i hb G)]

theorem raw_covariance (i : Row) (G : Measure (ℝ × ℝ)) {b : ℝ} (hb : 0 < b)
    (F H : MixedLaw.Pair → ℝ) (hF : Measurable F) (hH : Measurable H) :
    covariance (fun r => F (point (xi i) b r))
      (fun r => H (point (xi i) b r)) (source i G)=
      covariance F H (MixedLaw.law i (MixedLaw.physicalLowerLaw i b G)) := by
  have hh := covariance_map (μ := source i G)
    hF.aestronglyMeasurable hH.aestronglyMeasurable
    (measurable_point (xi i) b).aemeasurable
  rw [map_source i G hb] at hh
  exact hh.symm

theorem demand_sign_covariance (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) : covariance (demand (xi i) b) sign (source i G)=0 := by
  letI := MixedLaw.physicalLowerLaw_probability i hb G
  have hh := raw_covariance i G hb Prod.fst Prod.snd measurable_fst measurable_snd
  change covariance (demand (xi i) b) sign (source i G)=_ at hh
  rw [hh,MixedLaw.demand_sign_covariance i _ (MixedLaw.physicalLowerLaw_bounds i hb G)]

def mean (i : Row) (G : Measure (ℝ × ℝ)) (b : ℝ) : ℝ :=
  ∫ r, demand (xi i) b r ∂source i G

def centered (i : Row) (G : Measure (ℝ × ℝ)) (b : ℝ) : Fin 2 → RowRival → ℝ :=
  ![fun r => demand (xi i) b r-mean i G b,sign]

def variances (i : Row) (G : Measure (ℝ × ℝ)) (b : ℝ) : Fin 2 → ℝ :=
  ![variance (demand (xi i) b) (source i G),1-cutoff i]

theorem centered_measurable (i : Row) (G : Measure (ℝ × ℝ)) (b : ℝ) :
    ∀ j, Measurable (centered i G b j) := by
  intro j
  fin_cases j
  · exact (measurable_demand _ _).sub_const _
  · exact measurable_sign

theorem centered_bounds_and_mean (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) :
    (∀ j r, |centered i G b j r| ≤ 1) ∧
      (∀ j, ∫ r, centered i G b j r ∂source i G=0) := by
  have hunit := demand_bounds (xi_pos i) hb
  have hmean : mean i G b ∈ Icc (0:ℝ) 1 := RivalGood.integral_unit_bounds
    (source i G) (measurable_demand _ _).aemeasurable (Filter.Eventually.of_forall hunit)
  have hi : Integrable (demand (xi i) b) (source i G) :=
    Integrable.of_mem_Icc 0 1 (measurable_demand _ _).aemeasurable
      (Filter.Eventually.of_forall hunit)
  constructor
  · intro j r
    fin_cases j
    · change |demand (xi i) b r-mean i G b| ≤ 1
      rw [abs_le]
      constructor <;> linarith [(hunit r).1,(hunit r).2,hmean.1,hmean.2]
    · exact sign_bounds r
  · intro j
    fin_cases j
    · change (∫ r, demand (xi i) b r-mean i G b ∂source i G)=0
      rw [integral_sub hi (integrable_const _),integral_const]
      simp [mean]
    · exact sign_mean i G hb

theorem centered_covariance (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) :
    ∀ j k, covariance (centered i G b j) (centered i G b k) (source i G)=
      if j=k then variances i G b j else 0 := by
  letI := MixedLaw.physicalLowerLaw_probability i hb G
  have hi : Integrable (demand (xi i) b) (source i G) :=
    Integrable.of_mem_Icc 0 1 (measurable_demand _ _).aemeasurable
      (Filter.Eventually.of_forall (demand_bounds (xi_pos i) hb))
  have hvar : variance sign (source i G)=1-cutoff i := by
    have he := (point_preserving i G hb).variance_fun_comp measurable_snd.aemeasurable
    change variance sign (source i G)=_ at he
    rw [he,MixedLaw.sign_variance i _ (MixedLaw.physicalLowerLaw_bounds i hb G)]
  intro j k
  fin_cases j <;> fin_cases k
  · change covariance (fun r => demand (xi i) b r-mean i G b)
      (fun r => demand (xi i) b r-mean i G b) (source i G) = variance (demand (xi i) b) (source i G)
    rw [covariance_sub_const_left hi,covariance_sub_const_right hi,
      covariance_self (measurable_demand _ _).aemeasurable]
  · change covariance (fun r => demand (xi i) b r-mean i G b) sign (source i G)=0
    rw [covariance_sub_const_left hi,demand_sign_covariance i G hb]
  · change covariance sign (fun r => demand (xi i) b r-mean i G b) (source i G)=0
    rw [covariance_comm,covariance_sub_const_left hi,demand_sign_covariance i G hb]
  · change covariance sign sign (source i G)=1-cutoff i
    rw [covariance_self measurable_sign.aemeasurable,hvar]

def draws {N : ℕ} (ω : Fin N → RowRival) : ℕ :=
  (classCount 2 ω-classCount 3 ω)+(classCount 3 ω-classCount 2 ω)

theorem sign_count {N : ℕ} (ω : Fin N → RowRival) :
    (∑ j, sign (ω j))=(classCount 2 ω:ℝ)-(classCount 3 ω:ℝ) := by
  have he (r : RowRival) : sign r=(if r.1=2 then (1:ℝ) else 0)-
      (if r.1=3 then (1:ℝ) else 0) := by
    unfold sign
    generalize r.1=k
    fin_cases k <;> norm_num [Fin.ext_iff]
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  simp [classCount]

theorem draws_eq_abs {N : ℕ} (ω : Fin N → RowRival) :
    (draws ω:ℝ)=|∑ j, sign (ω j)| := by
  rw [sign_count]
  rcases le_total (classCount 2 ω) (classCount 3 ω) with h | h
  · simp only [draws,Nat.sub_eq_zero_of_le h,zero_add,Nat.cast_sub h]
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · simp only [draws,Nat.sub_eq_zero_of_le h,add_zero,Nat.cast_sub h]
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

theorem draws_le {N : ℕ} (ω : Fin N → RowRival) : draws ω ≤ N := by
  have hc : classCount 2 ω+classCount 3 ω ≤ N := by
    unfold classCount
    rw [← Finset.sum_add_distrib]
    have hh : (∑ j : Fin N,
        ((if (ω j).1=2 then 1 else 0)+(if (ω j).1=3 then 1 else 0))) ≤
        ∑ _j : Fin N, (1:ℕ) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h2 : (ω j).1=2
      · simp [h2]
      · simp only [if_neg h2,zero_add]
        split_ifs <;> norm_num
    simpa using hh
  unfold draws
  omega

theorem measurable_draws (N : ℕ) : Measurable (draws : (Fin N → RowRival) → ℕ) := by
  have hc (k : Fin 4) : Measurable (classCount k : (Fin N → RowRival) → ℕ) := by
    unfold classCount
    apply Finset.measurable_sum
    intro j _
    exact Measurable.ite
      (measurableSet_eq_fun ((measurable_pi_apply j).fst) measurable_const)
      measurable_const measurable_const
  exact ((hc 2).sub (hc 3)).add ((hc 3).sub (hc 2))

theorem integral_lower_statistic (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable (fun p => f p.2) G) :
    (∫ r, RivalGood.lowerTest f r ∂source i G)=cutoff i*(∫ p, f p.2 ∂G) := by
  let ν := G.map Prod.snd
  let L : ℝ → RowRival := fun b => (0,b)
  have hL : Measurable L := measurable_const.prodMk measurable_id
  have hfν : Integrable f ν :=
    (integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable).mpr hi
  have hl : Integrable (RivalGood.lowerTest f) (ν.map L) := by
    apply (integrable_map_measure (RivalGood.measurable_lowerTest hf).aestronglyMeasurable hL.aemeasurable).mpr
    change Integrable (fun x => if (0:Fin 4)=0 then f x else 0) ν
    simpa only [ite_true] using hfν
  have h2 : Integrable (RivalGood.lowerTest f) (Measure.dirac ((2:Fin 4),(0:ℝ))) := integrable_dirac (by finiteness)
  have h3 : Integrable (RivalGood.lowerTest f) (Measure.dirac ((3:Fin 4),(0:ℝ))) := integrable_dirac (by finiteness)
  change (∫ r, RivalGood.lowerTest f r ∂(
    ENNReal.ofReal (cutoff i) • ν.map L+
    ENNReal.ofReal 0 • Measure.dirac ((1:Fin 4),(0:ℝ))+
    ENNReal.ofReal ((1-cutoff i)/2) • Measure.dirac ((2:Fin 4),(0:ℝ))+
    ENNReal.ofReal ((1-cutoff i)/2) • Measure.dirac ((3:Fin 4),(0:ℝ))))=_
  simp only [ENNReal.ofReal_zero,zero_smul,add_zero]
  rw [integral_add_measure ((hl.smul_measure ENNReal.ofReal_ne_top).add_measure
      (h2.smul_measure ENNReal.ofReal_ne_top)) (h3.smul_measure ENNReal.ofReal_ne_top),
    integral_add_measure (hl.smul_measure ENNReal.ofReal_ne_top) (h2.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure,integral_smul_measure,integral_smul_measure,
    integral_dirac,integral_dirac,integral_map hL.aemeasurable
      (RivalGood.measurable_lowerTest hf).aestronglyMeasurable]
  simp only [L,RivalGood.lowerTest,ite_true,show (2:Fin 4)≠0 by decide,
    show (3:Fin 4)≠0 by decide,if_false,
    ENNReal.toReal_ofReal (cutoff_pos i).le,smul_eq_mul]
  simp only [mul_zero,add_zero]
  change cutoff i * (∫ x, f x ∂G.map Prod.snd) = _
  rw [integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]

end FCAppendix.Affine.Uniform06.RawMixedSource
