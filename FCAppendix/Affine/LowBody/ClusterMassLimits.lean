import FCAppendix.Affine.LowBody.NoisyBaseLaw
import Mathlib.MeasureTheory.Measure.Portmanteau

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical Filter Topology

theorem mass_tendsto_of_real_tendsto
    (mu : ℕ→ProbabilityMeasure ℝ) (E : Set ℝ) (p : ℝ)
    (ht : Tendsto (fun j=>(mu j : Measure ℝ).real E) atTop (𝓝 p)) :
    Tendsto (fun j=>(mu j : Measure ℝ) E) atTop (𝓝 (ENNReal.ofReal p)) :=
  (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
    (Eventually.of_forall (fun j=>ENNReal.ofReal_toReal (measure_ne_top (mu j : Measure ℝ) E)))

theorem open_mass_limit_lower (mu : ℕ→ProbabilityMeasure ℝ) (mu₀ : ProbabilityMeasure ℝ)
    (hmu : Tendsto mu atTop (𝓝 mu₀)) (E : Set ℝ) (hE : IsOpen E)
    (p : ℝ) (hp : 0≤p)
    (ht : Tendsto (fun j=>(mu j : Measure ℝ).real E) atTop (𝓝 p)) :
    (mu₀ : Measure ℝ).real E≤p := by
  have hh:=ProbabilityMeasure.le_liminf_measure_open_of_tendsto hmu hE
  rw [(mass_tendsto_of_real_tendsto mu E p ht).liminf_eq] at hh
  have hb : (mu₀ : Measure ℝ) E≤ENNReal.ofReal p := by
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hh
  exact ENNReal.toReal_le_of_le_ofReal hp hb

theorem closed_mass_limit_upper (mu : ℕ→ProbabilityMeasure ℝ) (mu₀ : ProbabilityMeasure ℝ)
    (hmu : Tendsto mu atTop (𝓝 mu₀)) (E : Set ℝ) (hE : IsClosed E)
    (p : ℝ)
    (ht : Tendsto (fun j=>(mu j : Measure ℝ).real E) atTop (𝓝 p)) :
    p≤(mu₀ : Measure ℝ).real E := by
  have hh:=ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hmu hE
  rw [(mass_tendsto_of_real_tendsto mu E p ht).limsup_eq] at hh
  have hb : ENNReal.ofReal p≤(mu₀ : Measure ℝ) E := by
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hh
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top (mu₀ : Measure ℝ) E)).mp hb

theorem exists_three_cluster_mass_subsequence
    (H G : ℕ→ProbabilityMeasure ℝ) (G₀ : ProbabilityMeasure ℝ)
    (hH : Tendsto H atTop (𝓝 G₀)) (hG : Tendsto G atTop (𝓝 G₀))
    (E B C : Set ℝ) (hE : IsOpen E) (hB : IsClosed B) (hC : IsClosed C) :
    ∃(phi : ℕ→ℕ),StrictMono phi ∧ ∃p q r : unitInterval,
      Tendsto (fun j=>(H (phi j) : Measure ℝ).real E) atTop (𝓝 p.1) ∧
      Tendsto (fun j=>(G (phi j) : Measure ℝ).real B) atTop (𝓝 q.1) ∧
      Tendsto (fun j=>(G (phi j) : Measure ℝ).real C) atTop (𝓝 r.1) ∧
      (G₀ : Measure ℝ).real E≤p.1 ∧ q.1≤(G₀ : Measure ℝ).real B ∧ r.1≤(G₀ : Measure ℝ).real C := by
  let mass : ℕ→unitInterval×unitInterval×unitInterval:=fun j=>
    (⟨(H j : Measure ℝ).real E,measureReal_nonneg,measureReal_le_one⟩,
      ⟨(G j : Measure ℝ).real B,measureReal_nonneg,measureReal_le_one⟩,
      ⟨(G j : Measure ℝ).real C,measureReal_nonneg,measureReal_le_one⟩)
  obtain ⟨m,phi,hphi,hlim⟩:=CompactSpace.tendsto_subseq mass
  have hp : Tendsto (fun j=>(H (phi j) : Measure ℝ).real E) atTop (𝓝 m.1.1):=
    continuous_fst.subtype_val.continuousAt.tendsto.comp hlim
  have hq : Tendsto (fun j=>(G (phi j) : Measure ℝ).real B) atTop (𝓝 m.2.1.1):=
    (continuous_fst.comp continuous_snd).subtype_val.continuousAt.tendsto.comp hlim
  have hr : Tendsto (fun j=>(G (phi j) : Measure ℝ).real C) atTop (𝓝 m.2.2.1):=
    (continuous_snd.comp continuous_snd).subtype_val.continuousAt.tendsto.comp hlim
  exact ⟨phi,hphi,m.1,m.2.1,m.2.2,hp,hq,hr,
    open_mass_limit_lower (H ∘ phi) G₀ (hH.comp hphi.tendsto_atTop) E hE m.1.1 m.1.property.1 hp,
    closed_mass_limit_upper (G ∘ phi) G₀ (hG.comp hphi.tendsto_atTop) B hB m.2.1.1 hq,
    closed_mass_limit_upper (G ∘ phi) G₀ (hG.comp hphi.tendsto_atTop) C hC m.2.2.1 hr⟩

theorem atom_bound_of_finite_cluster_estimates
    (H G : ℕ→ProbabilityMeasure ℝ) (G₀ : ProbabilityMeasure ℝ)
    (hH : Tendsto H atTop (𝓝 G₀)) (hG : Tendsto G atTop (𝓝 G₀))
    (E B C : Set ℝ) (hE : IsOpen E) (hB : IsClosed B) (hC : IsClosed C)
    (b A D err : ℝ) (hb : b∈E) (hA : 0<A) (hD : 0≤D) (herr : 0≤err)
    (hfinite : ∀ᶠj : ℕ in atTop,
      (H j : Measure ℝ).real E ^ 2*A≤(H j : Measure ℝ).real E*
        (D*((G j : Measure ℝ).real B+(G j : Measure ℝ).real C)+err)) :
    (G₀ : Measure ℝ).real {b}*A≤D*((G₀ : Measure ℝ).real B+(G₀ : Measure ℝ).real C)+err := by
  obtain ⟨phi,hphi,p,q,r,hp,hq,hr,hplo,hqhi,hrhi⟩:=
    exists_three_cluster_mass_subsequence H G G₀ hH hG E B C hE hB hC
  have hpoly : p.1^2*A≤p.1*(D*(q.1+r.1)+err) :=
    le_of_tendsto_of_tendsto ((hp.pow 2).mul_const A)
      (hp.mul (((hq.add hr).const_mul D).add_const err))
      (hphi.tendsto_atTop.eventually hfinite)
  have hmass : (G₀ : Measure ℝ).real {b}≤p.1 :=
    (measureReal_mono (singleton_subset_iff.mpr hb)).trans hplo
  have hrhs : D*(q.1+r.1)+err≤D*((G₀ : Measure ℝ).real B+(G₀ : Measure ℝ).real C)+err := by
    have hh:=mul_le_mul_of_nonneg_left (add_le_add hqhi hrhi) hD
    linarith only [hh]
  by_cases hp0 : p.1=0
  · have hz : (G₀ : Measure ℝ).real {b}=0:=le_antisymm (by simpa only [hp0] using hmass) measureReal_nonneg
    rw [hz,zero_mul]
    exact add_nonneg (mul_nonneg hD (add_nonneg measureReal_nonneg measureReal_nonneg)) herr
  · have hppos : 0<p.1:=lt_of_le_of_ne p.property.1 (Ne.symm hp0)
    have hcancel : p.1*A≤D*(q.1+r.1)+err := by nlinarith only [hpoly,hppos]
    exact (mul_le_mul_of_nonneg_right hmass hA.le).trans (hcancel.trans hrhs)

theorem iInter_shrinking_closedIntervals (b : ℝ) (r : ℕ→ℝ) (hr : ∀j,0≤r j)
    (ht : Tendsto r atTop (𝓝 0)) :
    (⋂j,Icc (b-r j) (b+r j))={b} := by
  ext x
  constructor
  · intro hx
    have hbound : ∀j,|x-b|≤r j := by
      intro j
      have hh:=mem_iInter.mp hx j
      exact abs_le.mpr ⟨by linarith [hh.1],by linarith [hh.2]⟩
    have hz : |x-b|≤0:=ge_of_tendsto ht (Eventually.of_forall hbound)
    exact mem_singleton_iff.mpr (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))))
  · intro hx
    have hx' : x=b:=mem_singleton_iff.mp hx
    subst x
    apply mem_iInter.mpr
    intro j
    exact ⟨by linarith [hr j],by linarith [hr j]⟩

theorem shrinking_closedInterval_mass (mu : Measure ℝ) [IsFiniteMeasure mu]
    (b : ℝ) (r : ℕ→ℝ) (hr : ∀j,0≤r j) (hanti : Antitone r)
    (ht : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun j=>mu.real (Icc (b-r j) (b+r j))) atTop (𝓝 (mu.real {b})) := by
  have hsets : Antitone (fun j=>Icc (b-r j) (b+r j)) := by
    intro i j hij x hx
    have hh:=hanti hij
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hm:=tendsto_measure_iInter_atTop (μ:=mu)
    (fun _=>measurableSet_Icc.nullMeasurableSet) hsets ⟨0,measure_ne_top mu _⟩
  rw [iInter_shrinking_closedIntervals b r hr ht] at hm
  exact (ENNReal.tendsto_toReal (measure_ne_top mu {b})).comp hm

end FCAppendix.Affine.LowBody
