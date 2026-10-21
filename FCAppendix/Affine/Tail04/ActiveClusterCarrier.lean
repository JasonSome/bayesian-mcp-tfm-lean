import FCAppendix.Affine.Tail04.NoisyCarrierIC
import FCAppendix.Affine.Tail04.TypicalFinitePromotion
import FCAppendix.Probability.Resample

noncomputable section
namespace FCAppendix.Affine.Tail04.ActiveClusterCarrier
open MeasureTheory ProbabilityTheory Set Filter Classical

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

def ordered (bid : X → ℝ) : Set (X×X) := {z | bid z.1≤ bid z.2}

lemma measurableSet_ordered (bid : X → ℝ) (hb : Measurable bid) :
    MeasurableSet (ordered bid) := measurableSet_le (hb.comp measurable_fst) (hb.comp measurable_snd)

lemma finite_pair_mass (μ : Measure X) [IsFiniteMeasure μ] :
    (μ.prod μ).real univ=(μ.real univ)^2 := by
  rw [measureReal_def,←Set.univ_prod_univ,Measure.prod_prod,ENNReal.toReal_mul]
  simp only [measureReal_def,pow_two]

theorem ordered_pair_mass_ge_half (μ : Measure X) [IsFiniteMeasure μ]
    (bid : X → ℝ) (hb : Measurable bid) :
    (μ.real univ)^2/2≤(μ.prod μ).real (ordered bid) := by
  let f : X×X → ℝ := fun z => if bid z.1≤ bid z.2 then 1 else 0
  let g : X×X → ℝ := fun z => if bid z.2≤ bid z.1 then 1 else 0
  have hf : Measurable f := Measurable.ite (measurableSet_ordered bid hb) measurable_const measurable_const
  have hg : Measurable g :=
    Measurable.ite (measurableSet_le (hb.comp measurable_snd) (hb.comp measurable_fst))
      measurable_const measurable_const
  have hfi : Integrable f (μ.prod μ) := Integrable.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ fun z => by dsimp [f];split_ifs <;> norm_num)
  have hgi : Integrable g (μ.prod μ) := Integrable.of_bound hg.aestronglyMeasurable 1
    (ae_of_all _ fun z => by dsimp [g];split_ifs <;> norm_num)
  have hswap : ∫ z,g z ∂μ.prod μ=∫ z,f z ∂μ.prod μ := by
    have hm := (Measure.measurePreserving_swap (μ:=μ) (ν:=μ)).map_eq
    have hi := integral_map (μ := μ.prod μ) measurable_swap.aemeasurable hf.aestronglyMeasurable
    rw [hm] at hi
    exact hi.symm
  have hpoint : ∀ z : X×X,(1:ℝ)≤ f z+g z := by
    intro z
    rcases le_total (bid z.1) (bid z.2) with h | h <;>
      simp only [f,g] <;> split_ifs <;> linarith
  have h := integral_mono (integrable_const 1) (hfi.add hgi) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hfi hgi,hswap,integral_const,smul_eq_mul,mul_one,finite_pair_mass] at h
  have he : (∫ z,f z ∂μ.prod μ)=(μ.prod μ).real (ordered bid) := by
    change (∫ z,(ordered bid).indicator (fun _ => (1:ℝ)) z ∂μ.prod μ)=_
    rw [integral_indicator (measurableSet_ordered bid hb),integral_const]
    simp only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,mul_one]
  rw [he] at h
  linarith

theorem conditional_bad_pair_bound (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (bad : (X×X)×Ω → Prop) (hm : MeasurableSet {z | bad z}) (ε : ℝ)
    (hbad : ∀ x : X×X,ν.real {ω | bad (x,ω)}≤ ε) :
    (∫ z,if bad z then (1:ℝ) else 0 ∂(μ.prod μ).prod ν)≤ ε*(μ.real univ)^2 := by
  let f : (X×X)×Ω → ℝ := fun z => if bad z then 1 else 0
  have hf : Measurable f := Measurable.ite hm measurable_const measurable_const
  have hfi : Integrable f ((μ.prod μ).prod ν) := Integrable.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ fun z => by dsimp [f];split_ifs <;> norm_num)
  have he (x : X×X) : (∫ ω,f (x,ω) ∂ν)=ν.real {ω | bad (x,ω)} := by
    have hs : MeasurableSet {ω | bad (x,ω)} := hm.preimage (measurable_const.prodMk measurable_id)
    change (∫ ω,({ω | bad (x,ω)} : Set Ω).indicator (fun _ => (1:ℝ)) ω ∂ν)=_
    rw [integral_indicator hs,integral_const]
    simp only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,mul_one]
  change (∫ z,f z ∂(μ.prod μ).prod ν)≤_
  rw [integral_prod _ hfi]
  calc
    _ ≤ ∫ _x : X×X,ε ∂μ.prod μ :=
      integral_mono hfi.integral_prod_left (integrable_const ε) (fun x => by rw [he];exact hbad x)
    _ = ε*(μ.real univ)^2 := by rw [integral_const,smul_eq_mul,finite_pair_mass];ring

theorem integrate_ordered_promotion (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (bid : X → ℝ) (hb : Measurable bid)
    (gain error : (X×X)×Ω → ℝ)
    (hgain : Integrable gain ((μ.prod μ).prod ν))
    (herror : Integrable error ((μ.prod μ).prod ν))
    (bad : (X×X)×Ω → Prop) (hm : MeasurableSet {z | bad z})
    (a loss ε : ℝ) (ha : 0≤ a) (hloss : 0≤ loss)
    (hbad : ∀ x : X×X,ν.real {ω | bad (x,ω)}≤ ε)
    (hpoint : ∀ᵐ z ∂(μ.prod μ).prod ν,
      a*(if bid z.1.1≤ bid z.1.2 then 1 else 0)-
        loss*(if bad z then 1 else 0)-error z≤ gain z) :
    (a/2-loss*ε)*(μ.real univ)^2-
      (∫ z,error z ∂(μ.prod μ).prod ν)≤∫ z,gain z ∂(μ.prod μ).prod ν := by
  let ord : (X×X)×Ω → ℝ := fun z => if bid z.1.1≤ bid z.1.2 then 1 else 0
  let badI : (X×X)×Ω → ℝ := fun z => if bad z then 1 else 0
  have ho : Measurable ord := Measurable.ite
    ((measurableSet_ordered bid hb).preimage measurable_fst) measurable_const measurable_const
  have hbi : Measurable badI := Measurable.ite hm measurable_const measurable_const
  have hoi : Integrable ord ((μ.prod μ).prod ν) := Integrable.of_bound ho.aestronglyMeasurable 1
    (ae_of_all _ fun z => by dsimp [ord];split_ifs <;> norm_num)
  have hbii : Integrable badI ((μ.prod μ).prod ν) := Integrable.of_bound hbi.aestronglyMeasurable 1
    (ae_of_all _ fun z => by dsimp [badI];split_ifs <;> norm_num)
  have hh := integral_mono_ae (((hoi.const_mul a).sub (hbii.const_mul loss)).sub herror) hgain hpoint
  simp only [Pi.sub_apply] at hh
  have hs : Integrable (fun x => a*ord x-loss*badI x) ((μ.prod μ).prod ν) :=
    (hoi.const_mul a).sub (hbii.const_mul loss)
  have hi0 : Integrable (fun x => a*ord x) ((μ.prod μ).prod ν) := hoi.const_mul a
  have hi1 : Integrable (fun x => loss*badI x) ((μ.prod μ).prod ν) := hbii.const_mul loss
  rw [integral_sub hs herror,integral_sub hi0 hi1,integral_const_mul,integral_const_mul] at hh
  have heo : (∫ z,ord z ∂(μ.prod μ).prod ν)=(μ.prod μ).real (ordered bid) := by
    have hc (x : X × X) : (∫ y : Ω, ord (x,y) ∂ν) =
        (if bid x.1 ≤ bid x.2 then (1:ℝ) else 0) := by
      change (∫ _y : Ω, (if bid x.1 ≤ bid x.2 then (1:ℝ) else 0) ∂ν) = _
      rw [integral_const]
      simp only [probReal_univ,one_smul]
    rw [integral_prod _ hoi]
    simp_rw [hc]
    change (∫ x,(ordered bid).indicator (fun _ => (1:ℝ)) x ∂μ.prod μ)=_
    rw [integral_indicator (measurableSet_ordered bid hb),integral_const]
    simp only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,mul_one]
  rw [heo] at hh
  have horder := mul_le_mul_of_nonneg_left (ordered_pair_mass_ge_half μ bid hb) ha
  have hbad' := mul_le_mul_of_nonneg_left (conditional_bad_pair_bound μ ν bad hm ε hbad) hloss
  change loss*(∫ z,badI z ∂(μ.prod μ).prod ν)≤_ at hbad'
  nlinarith only [hh,horder,hbad']

end FCAppendix.Affine.Tail04.ActiveClusterCarrier
