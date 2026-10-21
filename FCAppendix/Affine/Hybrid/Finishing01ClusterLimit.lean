import FCAppendix.Affine.Hybrid.Finishing01ClusterMeasures

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology Classical

theorem active_atom_zero_of_fixed_market_cluster_estimates
    (H G : ℕ→ ProbabilityMeasure ℝ) (G0 : ProbabilityMeasure ℝ)
    (hH : Tendsto H atTop (𝓝 G0)) (hG : Tendsto G atTop (𝓝 G0))
    (b : ℝ) {A B C : ℝ} (hA : 0<A) (hB : 0≤ B) (hBA : B<A) (hC : 0≤ C)
    (hfinite : ∀ err : ℝ,0<err→∃deltaMax : ℝ,0<deltaMax ∧
      ∀ delta : ℝ,0<delta→ delta<deltaMax→∀ᶠj : ℕ in atTop,
        A*(H j:Measure ℝ).real (Ioo (b-delta) (b+delta))^2 ≤
          B*(H j:Measure ℝ).real (Ioo (b-delta) (b+delta))*
            (G j:Measure ℝ).real (Icc (b-delta) (b+3*delta))+
          (H j:Measure ℝ).real (Ioo (b-delta) (b+delta))*(C*delta+err)) :
    (G0:Measure ℝ) {b}=0 := by
  let r : ℕ→ℝ := fun k => 1/((k:ℝ)+1)
  have hr (k : ℕ) : 0<r k := by dsimp [r];positivity
  have hranti : Antitone r := by
    intro i j hij
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hrzero : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hbound (k : ℕ) : (G0:Measure ℝ).real {b}*A ≤
      B*(G0:Measure ℝ).real (Icc (b-3*r k) (b+3*r k))+(C+1)*r k := by
    obtain ⟨deltaMax,hdmax,hf⟩ := hfinite (r k) (hr k)
    let delta := min (r k) (deltaMax/2)
    have hd : 0<delta := lt_min (hr k) (half_pos hdmax)
    have hdm : delta<deltaMax := (min_le_right _ _).trans_lt (half_lt_self hdmax)
    have hdr : delta≤ r k := min_le_left _ _
    have hineq := LowBody.atom_bound_of_finite_cluster_estimates H G G0 hH hG
      (Ioo (b-delta) (b+delta)) (Icc (b-delta) (b+3*delta)) ∅
      isOpen_Ioo isClosed_Icc isClosed_empty b A B (C*delta+r k)
      ⟨by linarith,by linarith⟩ hA hB (by positivity)
      ((hf delta hd hdm).mono (fun j hj => by
        simpa only [measureReal_empty,add_zero,mul_add,mul_comm,mul_left_comm,mul_assoc] using hj))
    simp only [measureReal_empty,add_zero] at hineq
    have hset : Icc (b-delta) (b+3*delta) ⊆ Icc (b-3*r k) (b+3*r k) := by
      intro x hx
      constructor <;> linarith [hx.1,hx.2,hr k]
    have hmass := measureReal_mono (μ:=(G0:Measure ℝ)) hset
    have he := mul_le_mul_of_nonneg_left hdr hC
    have hm := mul_le_mul_of_nonneg_left hmass hB
    linarith
  have hr3 : Tendsto (fun k => 3*r k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hrzero.const_mul 3
  have hmass := LowBody.shrinking_closedInterval_mass (G0:Measure ℝ) b
    (fun k => 3*r k) (fun k => by positivity) (by
      intro i j hij
      exact mul_le_mul_of_nonneg_left (hranti hij) (by norm_num)) hr3
  have hlim : (G0:Measure ℝ).real {b}*A ≤ B*(G0:Measure ℝ).real {b} := by
    have hh := le_of_tendsto_of_tendsto tendsto_const_nhds
      ((hmass.const_mul B).add (hrzero.const_mul (C+1)))
      (Eventually.of_forall hbound)
    simpa only [mul_zero,add_zero] using hh
  have hz : (G0:Measure ℝ).real {b}=0 := by
    have hnn : 0≤(G0:Measure ℝ).real {b} := measureReal_nonneg
    nlinarith
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top (G0:Measure ℝ) {b})

theorem singleton_zero_of_real_zero {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (x : X) (hz : mu.real {x}=0) : mu {x}=0 :=
  ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top mu {x})

theorem nullSingleton_map_of_supported_singletons {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (mu : Measure X) [IsFiniteMeasure mu] (f : X→ Y) (hf : Measurable f)
    (S : Set Y) (_hS : MeasurableSet S) (hsupport : ∀ᵐx ∂mu,f x∈ S)
    (hzero : ∀ y∈ S,(mu.map f) {y}=0) : NullSingletonClass (mu.map f) := by
  constructor
  intro y
  by_cases hy : y∈ S
  · exact hzero y hy
  rw [Measure.map_apply hf (measurableSet_singleton y)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hsupport] with x hx
  intro he
  have hxy : f x=y := he
  exact hy (hxy ▸ hx)

end FCAppendix.Affine.Hybrid
