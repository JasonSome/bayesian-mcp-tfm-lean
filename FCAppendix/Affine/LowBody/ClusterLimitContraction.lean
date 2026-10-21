import FCAppendix.Affine.LowBody.ClusterMassLimits
import FCAppendix.Affine.LowBody.ClusterIteration

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem atom_bound_of_varying_finite_cluster_estimates
    (H G : ℕ→ProbabilityMeasure ℝ) (G₀ : ProbabilityMeasure ℝ)
    (hH : Tendsto H atTop (𝓝 G₀)) (hG : Tendsto G atTop (𝓝 G₀))
    (E B C : Set ℝ) (hE : IsOpen E) (hB : IsClosed B) (hC : IsClosed C)
    (b A D err : ℝ) (hb : b∈E) (hA : 0<A) (hD : 0≤D) (herr : 0≤err)
    (Aj Dj ej : ℕ→ℝ) (hAj : Tendsto Aj atTop (𝓝 A))
    (hDj : Tendsto Dj atTop (𝓝 D)) (hej : Tendsto ej atTop (𝓝 err))
    (hfinite : ∀ᶠj : ℕ in atTop,
      (H j : Measure ℝ).real E ^ 2*Aj j≤(H j : Measure ℝ).real E*
        (Dj j*((G j : Measure ℝ).real B+(G j : Measure ℝ).real C)+ej j)) :
    (G₀ : Measure ℝ).real {b}*A≤D*((G₀ : Measure ℝ).real B+(G₀ : Measure ℝ).real C)+err := by
  obtain ⟨phi,hphi,p,q,r,hp,hq,hr,hplo,hqhi,hrhi⟩:=
    exists_three_cluster_mass_subsequence H G G₀ hH hG E B C hE hB hC
  have hpoly : p.1^2*A≤p.1*(D*(q.1+r.1)+err) :=
    le_of_tendsto_of_tendsto ((hp.pow 2).mul (hAj.comp hphi.tendsto_atTop))
      (hp.mul (((hDj.comp hphi.tendsto_atTop).mul (hq.add hr)).add
        (hej.comp hphi.tendsto_atTop))) (hphi.tendsto_atTop.eventually hfinite)
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

theorem atom_bound_of_shrinking_envelopes
    (mu : Measure ℝ) [IsFiniteMeasure mu] {b κ A D K : ℝ}
    (hb : 0<b) (hA : 0<A)
    (r : ℕ→ℝ) (hr : ∀j,0≤r j) (hanti : Antitone r)
    (hrt : Tendsto r atTop (𝓝 0)) (hκ : 0≤κ)
    (hbound : ∀ᶠj : ℕ in atTop,
      mu.real {b}*((b-r j)*A)≤(b+3*r j)*D*
        (mu.real (Icc (b-3*r j) (b+3*r j))+
          mu.real (Icc (κ*b-3*κ*r j) (κ*b+3*κ*r j)))+K*r j) :
    mu.real {b}≤(D/A)*(mu.real {b}+mu.real {κ*b}) := by
  have ht₁:=shrinking_closedInterval_mass mu b (fun j=>3*r j)
    (fun j=>mul_nonneg (by norm_num) (hr j)) (fun i j hij=>by simpa using mul_le_mul_of_nonneg_left (hanti hij) (by norm_num : (0:ℝ)≤3))
    (by simpa using hrt.const_mul 3)
  have ht₂:=shrinking_closedInterval_mass mu (κ*b) (fun j=>3*κ*r j)
    (fun j=>mul_nonneg (mul_nonneg (by norm_num) hκ) (hr j))
    (fun i j hij=>mul_le_mul_of_nonneg_left (hanti hij) (mul_nonneg (by norm_num) hκ))
    (by simpa using hrt.const_mul (3*κ))
  have hleft : Tendsto (fun j=>mu.real {b}*((b-r j)*A)) atTop
      (𝓝 (mu.real {b}*(b*A))) := by
    simpa using (((tendsto_const_nhds (x:=b)).sub hrt).mul_const A).const_mul (mu.real {b})
  have hright : Tendsto (fun j=>(b+3*r j)*D*
      (mu.real (Icc (b-3*r j) (b+3*r j))+
        mu.real (Icc (κ*b-3*κ*r j) (κ*b+3*κ*r j)))+K*r j) atTop
      (𝓝 (b*D*(mu.real {b}+mu.real {κ*b}))) := by
    simpa using (((tendsto_const_nhds (x:=b)).add (hrt.const_mul 3)).mul_const D).mul
      (ht₁.add ht₂) |>.add (hrt.const_mul K)
  have hl:=le_of_tendsto_of_tendsto hleft hright hbound
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hA).mpr
  apply (mul_le_mul_iff_right₀ hb).mp
  nlinarith only [hl]

end FCAppendix.Affine.LowBody
