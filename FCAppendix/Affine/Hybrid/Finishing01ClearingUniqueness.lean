import FCAppendix.Affine.Hybrid.Finishing01ClearingScalar

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open MeasureTheory Set Filter Topology Classical
open Existence.Distributional
namespace Primitives
variable (P : Primitives)

theorem continuous_foc_response (nu : ℝ) (q : P.Value → ℝ)
    (hq : ∀ v, q v ∈ Icc (0:ℝ) 1)
    (hphi : ∀ v, phi P.xi P.z (q v)=nu/(v:ℝ)) : Continuous q := by
  have hratio : Continuous (fun v : P.Value => nu/(v:ℝ)) :=
    continuous_const.div continuous_subtype_val (fun v => (P.value_pos v).ne')
  rw [continuous_iff_continuousAt]
  intro v
  rw [Metric.continuousAt_iff]
  intro eps heps
  obtain ⟨delta,hdelta,hd⟩ := (Metric.continuousAt_iff.mp hratio.continuousAt)
    (eps/P.inverseModulus) (div_pos heps P.inverseModulus_pos)
  refine ⟨delta,hdelta,?_⟩
  intro w hw
  have hh := hd hw
  rw [Real.dist_eq] at hh ⊢
  have hi := P.phi_inverse_distance (hq w) (hq v)
  rw [hphi w,hphi v] at hi
  exact hi.trans_lt ((mul_lt_mul_of_pos_left hh P.inverseModulus_pos).trans_eq
    (by field_simp [P.inverseModulus_pos.ne']))

theorem integrable_foc_response (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (nu : ℝ) (q : P.Value → ℝ) (hq : ∀ v, q v ∈ Icc (0:ℝ) 1)
    (hphi : ∀ v, phi P.xi P.z (q v)=nu/(v:ℝ)) : Integrable q mu := by
  apply Integrable.of_bound (P.continuous_foc_response nu q hq hphi).aestronglyMeasurable 1
  apply ae_of_all
  intro v
  rw [Real.norm_eq_abs,abs_of_nonneg (hq v).1]
  exact (hq v).2

theorem global_unique_interior_clearing (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (lam : P.Price) (hclear : (∫ v : P.Value, P.qResponse v lam ∂mu)=P.qbar)
    (nu : ℝ) (q : P.Value → ℝ) (hq : ∀ v, q v ∈ Ioo (0:ℝ) 1)
    (hphi : ∀ v, phi P.xi P.z (q v)=nu/(v:ℝ))
    (hqclear : (∫ v : P.Value, q v ∂mu)=P.qbar) : nu=(lam:ℝ) := by
  have hqbox (v : P.Value) : q v ∈ Icc (0:ℝ) 1 := ⟨(hq v).1.le,(hq v).2.le⟩
  have hrbox (v : P.Value) : P.qResponse v lam ∈ Icc (0:ℝ) 1 :=
    ⟨(P.qResponse_spec v lam).1.1.le,(P.qResponse_spec v lam).1.2.le⟩
  have hiq : Integrable q mu := P.integrable_foc_response mu nu q hqbox hphi
  have hir : Integrable (fun v : P.Value => P.qResponse v lam) mu :=
    P.integrable_foc_response mu lam (fun v => P.qResponse v lam) hrbox
      (fun v => P.qResponse_phi v lam)
  have hanti := (phi_strictAntiOn P.xi_pos P.xi_lt_one P.z_nonneg P.z_lt_one).antitoneOn
  rcases lt_trichotomy nu (lam:ℝ) with hlt | heq | hgt
  · have hpoint (v : P.Value) : P.qResponse v lam < q v := by
      have hratio := (div_lt_div_iff_of_pos_right (P.value_pos v)).mpr hlt
      rw [←hphi v,←P.qResponse_phi v lam] at hratio
      by_contra! hn
      have hh := hanti (hqbox v) (hrbox v) hn
      linarith
    have hmean := integral_lt_integral_of_ae_lt hir hiq (ae_of_all _ hpoint)
    rw [hclear,hqclear] at hmean
    exact (lt_irrefl _ hmean).elim
  · exact heq
  · have hpoint (v : P.Value) : q v < P.qResponse v lam := by
      have hratio := (div_lt_div_iff_of_pos_right (P.value_pos v)).mpr hgt
      rw [←P.qResponse_phi v lam,←hphi v] at hratio
      by_contra! hn
      have hh := hanti (hrbox v) (hqbox v) hn
      linarith
    have hmean := integral_lt_integral_of_ae_lt hiq hir (ae_of_all _ hpoint)
    rw [hqclear,hclear] at hmean
    exact (lt_irrefl _ hmean).elim

theorem interior_clearing_response_eq (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (lam : P.Price) (hclear : (∫ v : P.Value, P.qResponse v lam ∂mu)=P.qbar)
    (nu : ℝ) (q : P.Value → ℝ) (hq : ∀ v, q v ∈ Ioo (0:ℝ) 1)
    (hphi : ∀ v, phi P.xi P.z (q v)=nu/(v:ℝ))
    (hqclear : (∫ v : P.Value, q v ∂mu)=P.qbar) :
    ∀ v : P.Value, q v=P.qResponse v lam := by
  have hnu := P.global_unique_interior_clearing mu lam hclear nu q hq hphi hqclear
  intro v
  apply phi_injectiveOn P.xi_pos P.xi_lt_one P.z_nonneg P.z_lt_one
    ⟨(hq v).1.le,(hq v).2.le⟩
    ⟨(P.qResponse_spec v lam).1.1.le,(P.qResponse_spec v lam).1.2.le⟩
  rw [hphi v,P.qResponse_phi v lam,hnu]

theorem exists_unique_global_interior_clearing (mu : Measure P.Value) [IsProbabilityMeasure mu] :
    ∃! nu : ℝ, ∃ q : P.Value → ℝ,
      (∀ v, q v ∈ Ioo (0:ℝ) 1) ∧
      (∀ v, phi P.xi P.z (q v)=nu/(v:ℝ)) ∧
      (∫ v : P.Value, q v ∂mu)=P.qbar := by
  obtain ⟨lam,hclear,_hunique⟩ := P.exists_unique_clearing mu
  refine ⟨(lam:ℝ),⟨fun v => P.qResponse v lam,
    (fun v => (P.qResponse_spec v lam).1),(fun v => P.qResponse_phi v lam),hclear⟩,?_⟩
  rintro nu ⟨q,hq,hphi,hqclear⟩
  exact P.global_unique_interior_clearing mu lam hclear nu q hq hphi hqclear

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
