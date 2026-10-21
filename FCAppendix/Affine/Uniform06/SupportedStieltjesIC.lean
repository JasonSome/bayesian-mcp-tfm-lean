import FCAppendix.Affine.Uniform06.CompactStieltjes

noncomputable section
namespace FCAppendix.Affine.Uniform06.SupportedStieltjesIC

open MeasureTheory Set Filter Topology
open Rank CompactStieltjes

theorem supported_stieltjes_identity
    (F G : StieltjesFunction ℝ) [IsFiniteMeasure F.measure] [IsFiniteMeasure G.measure]
    (hF : Continuous F) (hG : Continuous G)
    (hFb : ∀ b : ℝ, F b ∈ Icc (0:ℝ) 1)
    (hGb : ∀ b : ℝ, G b ∈ Icc (0:ℝ) 1)
    (M : ℝ → ℝ) (hM : Continuous M)
    {C : Set ℝ} (hC : IsClosed C)
    {lo hi η q LD T : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi)
    (hCI : C ⊆ Ioc lo hi) (hη : η ∈ Icc (0:ℝ) 1)
    (hq : 0 < q) (hLD : 0 ≤ LD) (hT : 0 ≤ T)
    (hMb : ∀ b ∈ C, M b ∈ Icc (0:ℝ) T)
    (hrent : ∀ a ∈ C, q ≤ M a-a)
    (hdup : ∀ a ∈ Icc lo hi, ∀ b ∈ Icc lo hi, a ≤ b → G b-G a ≤ LD*(b-a))
    (hIC : ∀ a ∈ C, ∀ b ∈ Icc lo hi, b < M a →
      payoff η (M a) b (F b) (G b) ≤ payoff η (M a) a (F a) (G a)) :
    F.measure.restrict C ≪ volume ∧ G.measure.restrict C ≪ volume ∧
      (F.measure.restrict C).withDensityᵥ (fun b => M b-b)=
        (volume.restrict C).withDensityᵥ (fun b => F b+η*G b)+
          (G.measure.restrict C).withDensityᵥ (fun b => η*b) := by
  let KS : ℝ := 2*(2+hi*LD)/q
  have hhi0 : 0 < hi := hlo.trans_le hhi
  have hKS : 0 ≤ KS := by dsimp [KS]; positivity
  have hSac := restriction_ac_of_anchored_increments F hF hC hCI
    (half_pos hq) hKS (by
      intro a ha b haI hbI hab hstep
      by_cases he : a=b
      · subst b
        simp only [sub_self,mul_zero,le_refl]
      have hab' : a < b := lt_of_le_of_ne hab he
      have hb0 : 0 < b := hlo.trans_le hbI.1
      have hMa : q/2 ≤ M a-b := by linarith [hrent a ha]
      have hbM : b < M a := by linarith
      have hinc := IC_increment_upper (hIC a ha b hbI hbM)
      have hSnon : 0 ≤ F b-F a := sub_nonneg.mpr (F.mono hab)
      have hloS := mul_le_mul_of_nonneg_right hMa hSnon
      have hlevel : F a+η*G a ≤ 2 := by
        have hh := mul_le_mul_of_nonneg_left (hGb a).2 hη.1
        nlinarith [(hFb a).2, hη.2]
      have hΔ : 0 ≤ b-a := sub_nonneg.mpr hab
      have hlev := mul_le_mul_of_nonneg_left hlevel hΔ
      have hηb : η*b ≤ hi := by
        have hh := mul_le_mul_of_nonneg_right hη.2 hb0.le
        nlinarith [hbI.2]
      have hd := mul_le_mul_of_nonneg_left (hdup a haI b hbI hab)
        (mul_nonneg hη.1 hb0.le)
      have hdb := mul_le_mul_of_nonneg_right hηb (mul_nonneg hLD hΔ)
      have hKSeq : (q/2)*KS=2+hi*LD := by
        dsimp only [KS]
        field_simp [hq.ne']
      have hh : (q/2)*(F b-F a) ≤ (q/2)*(KS*(b-a)) := by
        rw [← mul_assoc,hKSeq]
        nlinarith
      exact le_of_mul_le_mul_left hh (half_pos hq))
  have hDac := restriction_ac_of_anchored_increments G hG hC hCI
    (show (0:ℝ) < 1 by norm_num) hLD (fun a _ b ha hb hab _ => hdup a ha b hb hab)
  refine ⟨hSac,hDac,?_⟩
  letI : IsFiniteMeasure (volume.restrict C) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (show C ⊆ Icc lo hi from fun b hb => ⟨(hCI hb).1.le,(hCI hb).2⟩)).trans_lt
      (show volume (Icc lo hi) < ⊤ by simp)
  have hne : ∀ᵐ b ∂volume, b ≠ hi := by
    rw [ae_iff]
    simp
  have hρS := Measure.rnDeriv_restrict F.measure volume hC.measurableSet
  have hρD := Measure.rnDeriv_restrict G.measure volume hC.measurableSet
  have hid : ∀ᵐ b ∂volume.restrict C,
      (M b-b)*((F.measure.restrict C).rnDeriv volume b).toReal=
        F b+η*G b+η*b*((G.measure.restrict C).rnDeriv volume b).toReal := by
    filter_upwards [ae_restrict_mem hC.measurableSet,
      ae_restrict_of_ae F.ae_hasDerivAt,ae_restrict_of_ae G.ae_hasDerivAt,
      ae_restrict_of_ae hρS,ae_restrict_of_ae hρD,ae_restrict_of_ae hne]
      with b hb hdF hdG hrF hrG hnb
    have hbI := hCI hb
    have hbhi : b < hi := lt_of_le_of_ne hbI.2 hnb
    have hbM : b < M b := by linarith [hrent b hb]
    have hloc : IsLocalMax (fun x => payoff η (M b) x (F x) (G x)) b := by
      filter_upwards [Ioo_mem_nhds hbI.1 (lt_min hbhi hbM)] with x hx
      exact hIC b hb x ⟨hx.1.le,hx.2.le.trans (min_le_left _ _)⟩
        (hx.2.trans_le (min_le_right _ _))
    have hd := hasDerivAt_payoff (η := η) (v := M b) hdF hdG
    have hz := hloc.deriv_eq_zero
    rw [hd.deriv] at hz
    rw [hrF,hrG,Set.indicator_of_mem hb,Set.indicator_of_mem hb]
    linarith
  have hAi : Integrable (fun b => F b+η*G b) (volume.restrict C) := by
    apply Integrable.mono' (integrable_const (2:ℝ))
      (hF.add (continuous_const.mul hG)).aestronglyMeasurable
    exact Eventually.of_forall fun b => by
      simp only [Pi.add_apply, Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (hFb b).1
        (mul_nonneg hη.1 (hGb b).1))]
      have hh := mul_le_mul_of_nonneg_left (hGb b).2 hη.1
      nlinarith [(hFb b).2, hη.2]
  exact vector_identity_of_actual_rn F.measure G.measure hC.measurableSet hSac hDac
    (fun b => M b-b) (fun b => F b+η*G b) (fun b => η*b)
    (hM.sub continuous_id).measurable (hF.add (continuous_const.mul hG)).measurable
    (continuous_const.mul continuous_id).measurable (T+hi) hi
    (fun b hb => by
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      have hm := hMb b hb
      have hbi := hCI hb
      constructor <;> linarith [hm.1,hm.2,hbi.1,hbi.2])
    (fun b hb => by
      have hb0 := hlo.trans (hCI hb).1
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hη.1 hb0.le)]
      have hh := mul_le_mul_of_nonneg_right hη.2 hb0.le
      nlinarith [(hCI hb).2]) hAi hid

end FCAppendix.Affine.Uniform06.SupportedStieltjesIC
