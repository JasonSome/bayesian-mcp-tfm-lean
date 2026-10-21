import FCAppendix.Affine.Uniform06.SourceEarlyFamily
import FCAppendix.Affine.Uniform06.SourceCoarseIncrement

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceUniformAmplification

open MeasureTheory Set Filter Topology LowBody
open Uniform07 LiteralExperiment SourceEarlyFamily SourcePrefixConstructor
open EarlyCoarseUniform SourceCoarseIncrement

section Family
variable {E : ℕ → Type*}
    (G : ∀ m,E m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,E m → GuardData)
    (cm : ∀ m,E m → (Fin (m-1) → Fin 4) → ℝ)

theorem original_box (i : Row) (h05 : EarlyMenuFields G g cm i) :
    ∀ m (e : E m),∀ᵐ p ∂(G m e:Measure (ℝ × ℝ)),
      p ∈ EarlyJointCompactness.box (cutoff i) (ReceiptGap.cap i) := by
  intro m e
  filter_upwards [EarlyRankCeiling.same_joint_value_support i (G m e:Measure (ℝ × ℝ))
    (h05.value_marginal m e),h05.permitted m e] with p hv hp
  have hf : 0 ≤ LowChernoff.physicalFloor i p.1 := by
    unfold LowChernoff.physicalFloor
    positivity
  exact ⟨hv,hf.trans hp.1,hp.2.trans (min_le_right _ _)⟩

theorem source_uniform_amplification (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hfields : ∀ m (e : E m),LiteralFields i (g m e))
    (hpsi : ∀ m (e : E m),
      (∫ p,PrefixRoot.sourcePsi i (g m e).rejectionRoot p.2
        ∂(G m e:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    {H : ℝ} (hHlo : cutoff i/2 ≤ H) (hH : H < entry i) :
    (∀ᶠ m in atTop,∀ e : E m,∀ b ∈ Icc (cutoff i/2) H,
      0 < sourceCanonicalMarginal i m (G m e) (g m e) (cm m e) b) ∧
    (∀ ε > (0:ℝ),∀ K > (0:ℝ),∀ᶠ m in atTop,∀ e : E m,
      ∀ b ∈ Icc (cutoff i/2) H,b+ε ≤ H →
        K*sourceCanonicalMarginal i m (G m e) (g m e) (cm m e) b <
          sourceCanonicalMarginal i m (G m e) (g m e) (cm m e) (b+ε)) := by
  let d := x i-H/cutoff i
  have ht := cutoff_pos i
  have hd : 0 < d := by
    dsimp [d]
    apply sub_pos.mpr
    exact (div_lt_iff₀ ht).mpr (by simpa only [entry] using hH)
  have hdmax : d ≤ x i-1/2 := by
    dsimp [d]
    have hh := (le_div_iff₀ ht).mpr (show (1/2:ℝ)*cutoff i ≤ H by nlinarith)
    linarith
  have hband (b : ℝ) : b/cutoff i ∈ Icc (1/2:ℝ) (x i-d) ↔
      b ∈ Icc (cutoff i/2) H := by
    dsimp [d]
    simp only [sub_sub_cancel,Set.mem_Icc]
    rw [le_div_iff₀ ht,div_le_div_iff_of_pos_right ht]
    constructor <;> intro h <;> exact ⟨by nlinarith [h.1],h.2⟩
  have ha := source_early_active G g cm i h05
  have hp := eventually_source_prefix G g cm i h05 hfields hpsi
  have hguard : ∀ᶠ m in atTop,∀ e : E m,(g m e).radius ≤ cutoff i/100 ∧
      0 < (g m e).margin ∧ 0 < (g m e).population ∧ 0 < (g m e).requiredDemand := by
    filter_upwards [hp] with m hm e
    exact ⟨(hm e).1,(hm e).2.1.margin_pos,(hm e).2.1.population_pos,
      (hm e).2.1.requiredDemand_pos⟩
  obtain ⟨θ,τ,Θ,A,hτ,hΘ,hcoarse⟩ := source_uniform_coarse E G g cm i hd hdmax
    h05.value_marginal (original_box G g cm i h05)
    (fun m e => (h05.permitted m e).mono fun _ h => h.2.trans (min_le_left _ _))
    ha h05.root_limit hguard
  let A' : ℝ := (A:ℝ)+1
  have hA : 0 < A' := by dsimp [A']; positivity
  have hpos : ∀ᶠ m in atTop,∀ e : E m,∀ b ∈ Icc (cutoff i/2) H,
      0 < sourceCanonicalMarginal i m (G m e) (g m e) (cm m e) b := by
    filter_upwards [hcoarse,eventually_ge_atTop (2:ℕ)] with m hm hm2 e b hb
    have hh := hm e (b/cutoff i) ((hband b).mpr hb)
    have hbounds := source_bounds i hm2 (G m e:Measure (ℝ × ℝ)) (g m e) (cm m e)
      hA hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2
    simpa only [div_mul_cancel₀ _ ht.ne'] using hbounds.1
  refine ⟨hpos,?_⟩
  intro ε hε K hK
  let κ := Real.exp (-Θ)*τ*TiltedGood.stripMass i/(xi i*ReceiptGap.cap i)
  have hκ : 0 < κ := by
    dsimp [κ]
    exact div_pos (mul_pos (mul_pos (Real.exp_pos _) hτ) (TiltedGood.stripMass_pos i))
      (mul_pos (xi_pos i) (ReceiptGap.cap_bounds i).1)
  have hN : Tendsto (fun m : ℕ => ((m-1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp PhysicalRates.rivals_tendsto
  have hlarge : ∀ᶠ m in atTop,K < (1/A'^2)*Real.exp (((m-1:ℕ):ℝ)*κ*ε) := by
    have hgrowth : Tendsto (fun m : ℕ => (1/A'^2)*Real.exp (((m-1:ℕ):ℝ)*κ*ε)) atTop atTop := by
      apply Filter.Tendsto.const_mul_atTop (by positivity)
      apply Real.tendsto_exp_atTop.comp
      exact (hN.atTop_mul_const hκ).atTop_mul_const hε
    exact hgrowth.eventually_gt_atTop K
  have haε := ha (EarlyRankCeiling.ceilingValue i-entry i)
    (sub_pos.mpr (EarlyRankCeiling.ceilingValue_bounds i).1.1)
    (cutoff i/10000) (by positivity)
  filter_upwards [hcoarse,hpos,hlarge,haε,eventually_ge_atTop (2:ℕ)]
    with m hm hpm hKm ham hm2 e b hb hraise
  have hbox := original_box G g cm i h05 m e
  have hcap : ∀ᵐ p ∂(G m e:Measure (ℝ × ℝ)),p.2 ≤ ReceiptGap.cap i :=
    hbox.mono fun _ h => h.2.2
  have hactive : ∀ᵐ p ∂(G m e:Measure (ℝ × ℝ)),
      p.1 ∈ Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ cutoff i/10000 := by
    have hid : entry i+(EarlyRankCeiling.ceilingValue i-entry i)=
        EarlyRankCeiling.ceilingValue i := by ring
    simpa only [hid] using ham e
  have hb' : b+ε ∈ Icc (cutoff i/2) H := ⟨by linarith [hb.1],hraise⟩
  have hc := hm e (b/cutoff i) ((hband b).mpr hb)
  have hc' := hm e ((b+ε)/cutoff i) ((hband (b+ε)).mpr hb')
  have hh := actual_increment i hm2 (G m e:Measure (ℝ × ℝ)) (h05.value_marginal m e)
    hcap hactive (g m e) (cm m e) hA hτ ((hband b).mpr hb).1
    ((div_lt_div_iff_of_pos_right ht).mpr (by linarith))
    (show ((b+ε)/cutoff i)*cutoff i ≤ EarlyRankCeiling.prefixEnd i by
      rw [div_mul_cancel₀ _ ht.ne']
      apply hraise.trans
      unfold EarlyRankCeiling.prefixEnd
      linarith)
    hc'.1 hc.2.1 hc.2.2 hc'.2.2
  have hex : (((b+ε)/cutoff i-b/cutoff i)*cutoff i)=ε := by
    field_simp [ht.ne']; ring
  rw [hex,div_mul_cancel₀ _ ht.ne',div_mul_cancel₀ _ ht.ne'] at hh
  have hratio := hKm.trans_le hh
  exact (lt_div_iff₀ (hpm e b hb)).mp hratio

end Family
end FCAppendix.Affine.Uniform06.SourceUniformAmplification
