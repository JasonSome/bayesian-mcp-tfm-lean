import FCAppendix.Affine.Uniform06.LiteralGuardEmpirical
import FCAppendix.Affine.Uniform06.EarlyMean

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralSeedRare

open Set MeasureTheory Filter
open scoped Topology BigOperators
open LowBody LiteralExperiment RawMixedSource RawTiltedSource RareEmpiricalReplacement
open FCAppendix.Affine.Uniform07 FCAppendix.ExponentialTilt

def seedSet (s : ℝ) : Set RowRival := {r | r.1=0 ∧ r.2 ≤ s}
def seedTest (s : ℝ) : RowRival → ℝ := (seedSet s).indicator (fun _ => 1)
def noRivalSeed {N : ℕ} (s : ℝ) : Set (Fin N → RowRival) :=
  {ω | ∀ j,ω j ∉ seedSet s}

theorem measurable_seedSet (s : ℝ) : MeasurableSet (seedSet s) :=
  (measurableSet_eq_fun measurable_fst measurable_const).inter
    (measurableSet_le measurable_snd measurable_const)

theorem measurable_seedTest (s : ℝ) : Measurable (seedTest s) :=
  measurable_const.indicator (measurable_seedSet s)

theorem seedTest_unit (s : ℝ) (r : RowRival) : seedTest s r ∈ Icc (0:ℝ) 1 := by
  by_cases hr : r ∈ seedSet s <;> simp [seedTest,hr]

theorem integral_seedTest (μ : Measure RowRival) (s : ℝ) :
    (∫ r,seedTest s r ∂μ)=μ.real (seedSet s) := by
  exact integral_indicator_one (measurable_seedSet s)

theorem measurable_noRivalSeed (N : ℕ) (s : ℝ) :
    MeasurableSet (@noRivalSeed N s) := by
  have he : @noRivalSeed N s=⋂ j : Fin N,{ω | ω j ∉ seedSet s} := by
    ext ω
    simp [noRivalSeed]
  rw [he]
  exact MeasurableSet.iInter fun j =>
    ((measurable_seedSet s).preimage (measurable_pi_apply j)).compl

theorem seeded_of_rival {N : ℕ} (g : GuardData) (c : ℕ) (b : ℝ)
    (ω : Fin N → RowRival) (j : Fin N) (hj : ω j ∈ seedSet g.seedCutoff) :
    seeded g (patternTemplate c (fun q => (ω q).1)) (rowBids b ω) := by
  refine ⟨j.succ,?_,?_⟩
  · simp [patternTemplate,rowLowList,patternRow,Fin.cons_succ,hj.1]
  · simpa only [rowBids,Fin.cons_succ,if_pos hj.1] using hj.2

theorem no_seed_subset {N : ℕ} (g : GuardData) (c : ℕ) (b : ℝ) :
    {ω : Fin N → RowRival | ¬seeded g
      (patternTemplate c (fun q => (ω q).1)) (rowBids b ω)} ⊆
        noRivalSeed g.seedCutoff := by
  intro ω hω j hj
  exact hω (seeded_of_rival g c b ω j hj)

theorem original_seed_mass (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G,p.2 ≤ p.1)
    {s : ℝ} (hs : 0 < s) (hst : s ≤ cutoff i) :
    s ≤ (source i G).real (seedSet s) := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hlow : G.real {p | p.1 ∈ Ioc (0:ℝ) s}=s/cutoff i := by
    have hmap : G.real {p | p.1 ∈ Ioc (0:ℝ) s}=
        (G.map Prod.fst).real (Ioc (0:ℝ) s) := by
      rw [Measure.real,Measure.real,Measure.map_apply measurable_fst measurableSet_Ioc]
      rfl
    rw [hmap,hvalue,EarlyMean.conditional_interval_mass i le_rfl hs.le hst,sub_zero]
  have hm : G {p | p.1 ∈ Ioc (0:ℝ) s} ≤ G {p | p.2 ≤ s} := by
    apply measure_mono_ae
    filter_upwards [hbid] with p hp hps
    exact hp.trans hps.2
  have hreal : s/cutoff i ≤ (G.map Prod.snd).real (Iic s) := by
    rw [← hlow]
    change (G {p | p.1 ∈ Ioc (0:ℝ) s}).toReal≤((G.map Prod.snd) (Iic s)).toReal
    rw [Measure.map_apply measurable_snd measurableSet_Iic]
    exact ENNReal.toReal_mono (measure_ne_top G _) hm
  have hsource := lowCluster_probability (cutoff i) 0 (1-cutoff i)
    (cutoff_pos i).le (G.map Prod.snd) (Iic s) measurableSet_Iic
  change (source i G).real (seedSet s)=cutoff i*(G.map Prod.snd).real (Iic s) at hsource
  rw [hsource]
  have hh := mul_le_mul_of_nonneg_left hreal (cutoff_pos i).le
  have he : cutoff i*(s/cutoff i)=s := by field_simp [(cutoff_pos i).ne']
  rwa [he] at hh

theorem tilted_seed_mass (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G,p.2 ≤ p.1)
    {s b θ Θ : ℝ} (hs : 0 < s) (hst : s ≤ cutoff i) (hb : 0 < b)
    (hθ : 0 ≤ θ) (hΘ : θ ≤ Θ) :
    Real.exp (-2*Θ)*s ≤ (tiltedSource i G b θ).real (seedSet s) := by
  letI := tiltedSource_probability i G hb θ
  have hh := (integral_tilted_bounds (source i G) (measurable_demand _ _)
    (ae_of_all _ fun r => demand_bounds (xi_pos i) hb r)
    (show |-θ| ≤ Θ by simpa [abs_of_nonneg hθ] using hΘ)
    ((integrable_const (1:ℝ)).indicator (measurable_seedSet s))
    (ae_of_all _ fun r => (seedTest_unit s r).1)).1
  change Real.exp (-2*Θ)*(∫ r,seedTest s r ∂source i G) ≤
    (∫ r,seedTest s r ∂tiltedSource i G b θ) at hh
  rw [integral_seedTest,integral_seedTest] at hh
  exact (mul_le_mul_of_nonneg_left (original_seed_mass i G hvalue hbid hs hst)
    (Real.exp_pos _).le).trans hh

theorem noRivalSeed_probability (μ : Measure RowRival) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N) {s q : ℝ} (hq : 0 ≤ q)
    (hm : q ≤ μ.real (seedSet s)) :
    (Measure.pi (fun _ : Fin N => μ)).real (noRivalSeed s) ≤
      Real.exp (-2*(N:ℝ)*q^2) := by
  have hsub : noRivalSeed s ⊆ {ω : Fin N → RowRival |
      q ≤ (∫ x,seedTest s x ∂μ)-(∑ j,seedTest s (ω j))/(N:ℝ)} := by
    intro ω hω
    have hz (j : Fin N) : seedTest s (ω j)=0 := by
      exact indicator_of_notMem (hω j) _
    change q≤(∫ x,seedTest s x ∂μ)-(∑ j,seedTest s (ω j))/(N:ℝ)
    simp only [hz,Finset.sum_const_zero,zero_div,sub_zero,integral_seedTest]
    exact hm
  exact (measureReal_mono hsub).trans
    (FCAppendix.Probability.iid_empiricalMean_lower_tail_le μ
      (measurable_seedTest s).aemeasurable (ae_of_all _ (seedTest_unit s)) N hN hq)

theorem source_noRivalSeed_probability (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G,p.2 ≤ p.1)
    {s b θ Θ : ℝ} (hs : 0 < s) (hst : s ≤ cutoff i) (hb : 0 < b)
    (hθ : 0 ≤ θ) (hΘ : θ ≤ Θ) (N : ℕ) (hN : 0 < N) :
    (Measure.pi (fun _ : Fin N => tiltedSource i G b θ)).real (noRivalSeed s) ≤
      Real.exp (-(2*(Real.exp (-2*Θ)*s)^2)*(N:ℝ)) := by
  letI := tiltedSource_probability i G hb θ
  have hh := noRivalSeed_probability (tiltedSource i G b θ) N hN
    (by positivity : 0 ≤ Real.exp (-2*Θ)*s)
    (tilted_seed_mass i G hvalue hbid hs hst hb hθ hΘ)
  simpa only [show -2*(N:ℝ)*(Real.exp (-2*Θ)*s)^2=
    -(2*(Real.exp (-2*Θ)*s)^2)*(N:ℝ) by ring] using hh

end FCAppendix.Affine.Uniform06.LiteralSeedRare
