import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Positive
import FCAppendix.Affine.Uniform06.SourceTinyFamily

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology
open FCAppendix.Affine Uniform06 Uniform06.LiteralExperiment Physical

def lowBenchmark (m : ℕ) : ℝ := Real.exp (-(3/1000000:ℝ)*(m:ℝ))/2

def lowDuplicateEnvelope (row : Uniform07.Row) (m : ℕ) : ℝ :=
  Real.exp (-(9/1000000:ℝ)*(m:ℝ))+
    Real.exp (SourceRankRates.equalRateConstant row-(m:ℝ)*LowChernoff.sourceGap row)

theorem lowBenchmark_pos (m : ℕ) : 0< lowBenchmark m := by
  unfold lowBenchmark
  positivity

theorem lowDuplicateEnvelope_nonnegative (row : Uniform07.Row) (m : ℕ) :
    0≤ lowDuplicateEnvelope row m := by
  unfold lowDuplicateEnvelope
  positivity

theorem source_low_rare_le_envelope (row : Uniform07.Row) {m : ℕ} (hm : 1≤ m) :
    LiteralLowDuplicate.pureRare m+LiteralLowDuplicate.equalRare row m≤
      lowDuplicateEnvelope row m := by
  apply add_le_add le_rfl
  exact Real.exp_le_exp.mpr (SourceRankRates.source_equal_exponent_upper row hm)

theorem low_relative_identity (row : Uniform07.Row) (m : ℕ) :
    lowDuplicateEnvelope row m/lowBenchmark m=
      2*(Real.exp (-(6/1000000:ℝ)*(m:ℝ))+
        Real.exp (SourceRankRates.equalRateConstant row-
          (m:ℝ)*SourceRankRates.equalRelativeGap row)) := by
  have hE : Real.exp (-(3/1000000:ℝ)*(m:ℝ))≠0:=Real.exp_ne_zero _
  have hp : Real.exp (-(9/1000000:ℝ)*(m:ℝ))=
      Real.exp (-(6/1000000:ℝ)*(m:ℝ))*Real.exp (-(3/1000000:ℝ)*(m:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have he : Real.exp (SourceRankRates.equalRateConstant row-(m:ℝ)*LowChernoff.sourceGap row)=
      Real.exp (SourceRankRates.equalRateConstant row-(m:ℝ)*SourceRankRates.equalRelativeGap row)*
        Real.exp (-(3/1000000:ℝ)*(m:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    unfold SourceRankRates.equalRelativeGap
    ring
  unfold lowDuplicateEnvelope lowBenchmark
  rw [hp,he]
  field_simp [hE]

theorem low_relative_tendsto (row : Uniform07.Row) :
    Tendsto (fun m=>lowDuplicateEnvelope row m/lowBenchmark m) atTop (𝓝 0) := by
  have hp:=LiteralWeakRent.tendsto_exp_affine_nat
    (by norm_num : (0:ℝ)<6/1000000) 0
  have he:=LiteralWeakRent.tendsto_exp_affine_nat
    (SourceRankRates.equalRelativeGap_pos row) (SourceRankRates.equalRateConstant row)
  have hh:=(hp.add he).const_mul 2
  have hswap (m : ℕ) : -(6/1000000:ℝ)*(m:ℝ)=-(m:ℝ)*(6/1000000) := by ring
  simpa only [zero_sub,←neg_mul,mul_zero,zero_add,low_relative_identity,hswap] using hh

section Family
variable {C : ℕ→ Type*}
    (G : ∀ m,C m→ ProbabilityMeasure (ℝ×ℝ))
    (g : ∀ m,C m→ GuardData)
    (cm : ∀ m,C m→(Fin (m-1)→ Fin 4)→ℝ)
variable {population : ℕ→ℕ}
    (Γ : ∀ k,FiniteGame (population k) 2 (Uniform07.capacity (population k)) unitInterval)

def low_family (row : Uniform07.Row)
    (h05 : SourceEarlyFamily.EarlyMenuFields G g cm row)
    (hr : EntryEarlyFamilyAdapter.RootFields G g row)
    (hatom : ∀ m (e : C m) b,((G m e:Measure (ℝ×ℝ)).map Prod.snd) {b}=0)
    (e : ∀ k,C (population k)) (hpopulation : Tendsto population atTop atTop)
    (hT : ∀ k (i : Fin (population k)),PositiveCountTransport row (G (population k) (e k))
      (g (population k) (e k)) (cm (population k) (e k)) (Γ k) i)
    (hzero : ∀ k (i : Fin (population k)),duplicate (Γ k) i 0≤
      duplicate (Γ k) i (Uniform07.cutoff row/2)) : LowFamily06 Γ row := by
  have hp:=SourceEarlyFamily.eventually_source_prefix G g cm row h05 hr.literal hr.rejection
  have hsmall : NativeSourceLowRoute.tinyEnd row≤ SourcePrefixConstructor.sortEnd row := by
    have hx : (501/1000:ℝ)< Uniform07.x row:=by
      cases row <;> norm_num [Uniform07.x,Uniform07.xQ]
    have ht:=Uniform07.cutoff_pos row
    unfold NativeSourceLowRoute.tinyEnd SourcePrefixConstructor.sortEnd Uniform07.entry
    nlinarith
  have hcap : ReceiptGap.cap row=Early.bidCap row := by
    rw [Early.cap_literal_product_formula]
    rfl
  have htopCap : sourceLowTop row≤ ReceiptGap.cap row := by
    rw [ReceiptGap.cap_scaled]
    have hh : (501/1000:ℝ)≤ ReceiptGap.capFactor row:=by
      cases row <;> norm_num [ReceiptGap.capFactor,Uniform07.x,Uniform07.xQ,
        Uniform07.kappa,Uniform07.kappaQ,Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]
    simpa only [sourceLowTop,mul_comm] using
      mul_le_mul_of_nonneg_left hh (Uniform07.cutoff_pos row).le
  have hcommon := hpopulation.eventually
    (hp.and ((SourceRankRates.eventually_Lm_lower row).and (eventually_ge_atTop 4)))
  refine {
    ell:=fun k=>lowBenchmark (population k)
    duplicateBound:=fun k=>lowDuplicateEnvelope row (population k)
    ellPositive:=Eventually.of_forall (fun k=>lowBenchmark_pos _)
    halfValue:=?_
    duplicate:=?_
    relativeError:=(low_relative_tendsto row).comp hpopulation }
  · filter_upwards [hcommon] with k hk
    let m:=population k
    let E:=e k
    have hprefix:=SourceTinyFamily.prefix_restrict (hk.1 E).2.1 hsmall
    have hlow : sourceLowTop row≤(g m E).multiplier-(g m E).radius := by
      simpa only [sourceLowTop,LowRankMeasures.extensionEnd] using (hk.1 E).2.2
    intro i v hv
    have hb : v/2∈Ioc (0:ℝ) (ReceiptGap.cap row):=
      ⟨half_pos hv.1,(source_half_value_cap row hv.2).1.trans hcap.symm.le⟩
    have hbTop : v/2≤ NativeSourceLowRoute.tinyEnd row:=
      (source_half_value_cap row hv.2).2
    have hS:=LiteralSuccessLower.source_actual_success_ge_Lm row hk.2.2
      (G m E) (g m E) hprefix (cm m E) (half_pos hv.1) hbTop (hatom m E (v/2))
    have hD:=(LiteralKernelDecomposition.source_first_duplicate_bounds row m (G m E) (g m E) (cm m E) (v/2)).2.1
    rw [(hT k i).mean hb]
    unfold lowBenchmark
    have hLm : Real.exp (-(3/1000000:ℝ)*(m:ℝ))≤SourceRankRates.Lm row m := by
      rw [show -(3/1000000:ℝ)*(m:ℝ)=-(m:ℝ)*(3/1000000) by ring]
      exact hk.2.1
    change SourceRankRates.Lm row m ≤ sourceSuccess row m (G m E) (g m E) (cm m E) (v/2) at hS
    change Real.exp (-(3/1000000:ℝ)*(m:ℝ))/2≤
      (sourceSuccess row m (G m E) (g m E) (cm m E) (v/2)+
       sourceDuplicate row m (G m E) (g m E) (cm m E) (v/2))/2
    linarith only [hLm,hS,hD]
  · filter_upwards [hcommon] with k hk
    let m:=population k
    let E:=e k
    have hprefix:=SourceTinyFamily.prefix_restrict (hk.1 E).2.1 hsmall
    have hlow : NativeSourceLowRoute.tinyEnd row≤(g m E).multiplier-(g m E).radius := by
      simpa only [NativeSourceLowRoute.tinyEnd,LowRankMeasures.extensionEnd] using (hk.1 E).2.2
    have hbound:=NativeSourceLowRoute.actual_duplicate_including_zero row hk.2.2
      (G m E) (h05.value_marginal m E)
      ((h05.permitted m E).mono (fun _ h=>h.1)) (hatom m E)
      (g m E) hprefix hlow (cm m E)
    have hpos (i : Fin m) (b : ℝ) (hb : b∈Ioc (0:ℝ) (sourceLowTop row)) :
        duplicate (Γ k) i b≤ lowDuplicateEnvelope row m := by
      rw [(hT k i).duplicate b ⟨hb.1,hb.2.trans htopCap⟩]
      exact (hbound b ⟨hb.1.le,hb.2⟩).trans
        (source_low_rare_le_envelope row (by omega))
    intro i b hb
    by_cases hz : b=0
    · subst b
      exact (hzero k i).trans (hpos i _ ⟨half_pos (Uniform07.cutoff_pos row),
        (source_half_value_cap row le_rfl).2⟩)
    · exact hpos i b ⟨lt_of_le_of_ne hb.1 (Ne.symm hz),hb.2⟩

end Family
end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
