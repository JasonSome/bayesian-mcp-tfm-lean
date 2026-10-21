import FCAppendix.Affine.Uniform06.CanonicalOptimizer
import FCAppendix.Affine.Uniform06.SourceUniformAmplification

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace FCAppendix.Affine.Uniform06.SourceCanonicalOptimizer

open MeasureTheory Set Filter Topology LowBody
open Uniform07 LiteralExperiment SourceEarlyFamily SourcePrefixConstructor
open CanonicalOptimizer SourceCanonicalRegularity SourceUniformAmplification

def leftBid (i : Row) (vmin : ℝ) : ℝ := (cutoff i/2+vmin)/2

section Family
variable {E : ℕ → Type*}
    (G : ∀ m,E m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,E m → GuardData)
    (cm : ∀ m,E m → (Fin (m-1) → Fin 4) → ℝ)

def chosen (i : Row) (vmin : ℝ) (m : ℕ) (e : E m) (v : ℝ) : ℝ :=
  if h : ∃ b,Optimal (sourceCanonicalMarginal i m (G m e) (g m e) (cm m e)) v b ∧
      leftBid i vmin < b ∧ b < v ∧
      0 < one (sourceCanonicalMarginal i m (G m e) (g m e) (cm m e)) v b
  then Classical.choose h else 0

theorem source_floor_zero {i : Row} {v : ℝ} (hv : v ≤ entry i) :
    LowChernoff.physicalFloor i v=0 := by
  have ht := cutoff_pos i
  have hh : (v-(entry i+cutoff i/400))/(cutoff i/400) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  unfold LowChernoff.physicalFloor
  rw [max_eq_left hh]
  norm_num

theorem original_optimizer (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hfields : ∀ m (e : E m),LiteralFields i (g m e))
    (hpsi : ∀ m (e : E m),
      (∫ p,PrefixRoot.sourcePsi i (g m e).rejectionRoot p.2
        ∂(G m e:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    {vmin vmax : ℝ} (hmin : cutoff i/2 < vmin) (hminmax : vmin ≤ vmax)
    (hmax : vmax < entry i) :
    ∀ᶠ m in atTop,∀ e : E m,∀ v ∈ Icc vmin vmax,
      let b := chosen G g cm i vmin m e v
      let C := sourceCanonicalMarginal i m (G m e) (g m e) (cm m e)
      Optimal C v b ∧ leftBid i vmin < b ∧ b < v ∧ 0 < one C v b ∧
      b ∈ Icc (LowChernoff.physicalFloor i v) (min v (ReceiptGap.cap i)) ∧
      ∀ a : ℝ,0 ≤ a → one C v a ≤ one C v b := by
  let a := leftBid i vmin
  let d := (a+vmin)/2
  have ht := cutoff_pos i
  have ha0 : 0 < a := by dsimp [a,leftBid]; linarith
  have halo : cutoff i/2 < a := by dsimp [a,leftBid]; linarith
  have hav : a < vmin := by dsimp [a,leftBid]; linarith
  have had : a < d := by dsimp [d]; linarith
  have hdv : d < vmin := by dsimp [d]; linarith
  have hHlo : cutoff i/2 ≤ vmax := hmin.le.trans hminmax
  let K := (vmax+1)/(vmin-d)
  have hK : 0 < K := by dsimp [K]; apply div_pos <;> linarith
  have hco := source_uniform_amplification G g cm i h05 hfields hpsi hHlo hmax
  have hp := eventually_source_prefix G g cm i h05 hfields hpsi
  filter_upwards [hco.1,hco.2 (d-a) (sub_pos.mpr had) K hK,hp]
    with m hpos hamp hprefix e v hv
  let C := sourceCanonicalMarginal i m (G m e) (g m e) (cm m e)
  have hf : ∀ᵐ p ∂(G m e:Measure (ℝ × ℝ)),LowChernoff.physicalFloor i p.1 ≤ p.2 :=
    (h05.permitted m e).mono fun _ h => h.1
  have hnon : ∀ b,0 ≤ C b := fun b => (source_canonical_nonnegative i m (G m e) (g m e) (cm m e) b).1
  have hmono := (source_canonical_monotone i m (G m e) hf (g m e) (hprefix e).2.1 (cm m e)).1
  have hsort : 0 ≤ sortEnd i := by unfold sortEnd; have := EarlyMean.entry_pos i; positivity
  have hvsort : v ≤ sortEnd i := by
    unfold sortEnd
    linarith [hv.2]
  have hcont := (source_canonical_lipschitz i m (G m e) hf (g m e)
    (hprefix e).2.1 hsort ha0 (cm m e)).continuousOn
  have haB : a ∈ Icc (cutoff i/2) vmax := ⟨halo.le,hav.le.trans hminmax⟩
  have hdB : d ∈ Icc (cutoff i/2) vmax := ⟨halo.le.trans had.le,hdv.le.trans hminmax⟩
  have hCa : 0 < C a := hpos e a haB
  have hCd : 0 < C d := hpos e d hdB
  have hgain : K*C a < C d := by
    have hh := hamp e a haB (show a+(d-a) ≤ vmax by linarith)
    have he : a+(d-a)=d := by ring
    simpa only [he] using hh
  have hbeat : v*C a < (v-d)*C d := by
    have hmul := mul_lt_mul_of_pos_left hgain (sub_pos.mpr hdv)
    have hcancel : (vmin-d)*K=vmax+1 := by dsimp [K]; field_simp [(sub_pos.mpr hdv).ne']
    rw [← mul_assoc,hcancel] at hmul
    have hfirst := mul_le_mul_of_nonneg_right hv.2 hCa.le
    have hlast := mul_le_mul_of_nonneg_right (sub_le_sub_right hv.1 d) hCd.le
    nlinarith
  obtain ⟨b,hb⟩ := exists_interior ha0 had (hdv.trans_le hv.1) hvsort hnon hmono hcont hCd hbeat
  have hex : ∃ b,Optimal C v b ∧ a < b ∧ b < v ∧ 0 < one C v b := ⟨b,hb⟩
  have hs : Optimal C v (chosen G g cm i vmin m e v) ∧
      a < chosen G g cm i vmin m e v ∧ chosen G g cm i vmin m e v < v ∧
      0 < one C v (chosen G g cm i vmin m e v) := by
    unfold chosen
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  refine ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,?_,?_⟩
  · rw [source_floor_zero (hv.2.trans hmax.le),min_eq_left
      (hv.2.trans (hmax.le.trans (ReceiptGap.entry_below_cap i).le))]
    exact hs.1.1
  · intro u hu
    by_cases huv : u ≤ v
    · exact hs.1.2 u ⟨hu,huv⟩
    · have hzero : one C v u ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (hnon u)
      exact hzero.trans hs.2.2.2.le

theorem original_optimizer_localization (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hfields : ∀ m (e : E m),LiteralFields i (g m e))
    (hpsi : ∀ m (e : E m),
      (∫ p,PrefixRoot.sourcePsi i (g m e).rejectionRoot p.2
        ∂(G m e:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    {vmin vmax : ℝ} (hmin : cutoff i/2 < vmin) (hminmax : vmin ≤ vmax)
    (hmax : vmax < entry i) :
    ∀ δ > (0:ℝ),∀ᶠ m in atTop,∀ e : E m,∀ v ∈ Icc vmin vmax,
      |chosen G g cm i vmin m e v-v| < δ := by
  have hco := source_uniform_amplification G g cm i h05 hfields hpsi
    (hmin.le.trans hminmax) hmax
  have ho := original_optimizer G g cm i h05 hfields hpsi hmin hminmax hmax
  intro δ hδ
  let K := vmax/(δ/2)+1
  have ht := cutoff_pos i
  have hvmax0 : 0 < vmax := (half_pos ht).trans (hmin.trans_le hminmax)
  have hK : 0 < K := by dsimp [K]; positivity
  filter_upwards [hco.1,ho,hco.2 (δ/2) (half_pos hδ) K hK]
    with m hpos hopt hamp e v hv
  let b := chosen G g cm i vmin m e v
  let C := sourceCanonicalMarginal i m (G m e) (g m e) (cm m e)
  have hs := hopt e v hv
  have hb : b ∈ Icc (cutoff i/2) vmax := by
    refine ⟨?_,hs.1.1.2.trans hv.2⟩
    have ha : cutoff i/2 < leftBid i vmin := by unfold leftBid; linarith
    exact ha.le.trans hs.2.1.le
  have hrent : v-b < 2*(δ/2) := rent_lt_of_amplification hs.1 (hpos e b hb)
    (half_pos hδ) (show v < (δ/2)*K by dsimp [K]; field_simp [(half_pos hδ).ne']; nlinarith [hv.2])
    (fun hraise => (hamp e b hb (hraise.trans hv.2)).le)
  rw [abs_of_nonpos (sub_nonpos.mpr hs.1.1.2)]
  linarith

theorem selected_optimizer_tendsto (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hfields : ∀ m (e : E m),LiteralFields i (g m e))
    (hpsi : ∀ m (e : E m),
      (∫ p,PrefixRoot.sourcePsi i (g m e).rejectionRoot p.2
        ∂(G m e:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    {vmin vmax v0 : ℝ} (hmin : cutoff i/2 < vmin) (hminmax : vmin ≤ vmax)
    (hmax : vmax < entry i) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (e : ∀ n,E (m n)) (v : ℕ → ℝ) (hv : ∀ n,v n ∈ Icc vmin vmax)
    (hvlim : Tendsto v atTop (𝓝 v0)) :
    Tendsto (fun n => chosen G g cm i vmin (m n) (e n) (v n)) atTop (𝓝 v0) := by
  have hd : Tendsto (fun n => chosen G g cm i vmin (m n) (e n) (v n)-v n)
      atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro δ hδ
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hm.eventually
      (original_optimizer_localization G g cm i h05 hfields hpsi hmin hminmax hmax δ hδ))
    refine ⟨N,fun n hn => ?_⟩
    simpa only [Real.dist_eq,sub_zero] using hN n hn (e n) (v n) (hv n)
  have hh := hd.add hvlim
  simpa only [sub_add_cancel,zero_add] using hh

end Family
end FCAppendix.Affine.Uniform06.SourceCanonicalOptimizer
