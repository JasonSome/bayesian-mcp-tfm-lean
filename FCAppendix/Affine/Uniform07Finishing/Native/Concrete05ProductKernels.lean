import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05ProductAlgebra
import FCAppendix.Affine.Uniform07Finishing.Native.ZeroCountMonotonicity

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine Crossover Crossover.Physical

theorem physical_moment_bounds {M c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame M 2 c Seed) (i : Fin M) {b : ℝ} (hb : 0≤ b) :
    0≤ duplicate Γ i b ∧ duplicate Γ i b≤ q Γ i b ∧
      q Γ i b≤ success Γ i b ∧ success Γ i b≤ 1 := by
  have hd:=duplicate_le_q Γ i hb
  have hs:=success_eq_two_q_sub_duplicate Γ i hb
  exact ⟨duplicate_nonneg Γ i b,hd,by linarith,
    ((problem Γ i).outcome (two b)).success_le_one⟩

theorem exact_native_zero_success_le_eighth {row : Uniform07.Row} {M : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row M) (hc : 1≤ Uniform07.capacity M)
    (i : Fin M) :
    success (exactNativeGame E hc (sourceLowerPriceCeiling row)) i 0≤
      success (exactNativeGame E hc (sourceLowerPriceCeiling row)) i
        (Uniform07.cutoff row/8) := by
  letI : NeZero M:=E.marketNeZero
  let test : Fin 3→ℝ:=fun r=>successIndicator r.val
  have htest : Monotone test := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> norm_num [test,successIndicator] at *
  have hzero : test 0=0 := by norm_num [test,successIndicator]
  have ht:=Uniform07.cutoff_pos row
  have he : 0< Uniform07.cutoff row/8:=by positivity
  have hz : Uniform07.cutoff row/2≤ E.law.rejectionRoot := by
    have hh:=(rejection_root_bounds E).1
    linarith
  have hG:=source_auxiliary_floor_guards row
  have hh:=sourceNativeGame_zero_broadcast_moment_le
    (width:=10*UniformFinite.Source.commonGuardMargin row)
    row E.cluster.market_two_le hc hG.1 hG.2.1 hG.2.2.1
    (multiplier_lower E) (auxiliary_guard row E.law) hz
    (UniformFinite.Source.common_guard_margin row)
    (lowerJoint E) (lowerJoint_value E) (lowerJoint_routes E)
    i (two 0) (two (Uniform07.cutoff row/8)) (two_bid le_rfl) (two_routes 0)
    (by simpa only [two_bid he.le] using he)
    (by simp only [two_bid he.le]; linarith) (two_routes _)
    test htest hzero
  simpa only [success,CountLaw.success,nativeGame,exactNativeGame,test] using hh

theorem eventual_native_product_kernels (row : Uniform07.Row)
    {tol : ℝ} (htol : 0< tol) :
    ∀ᶠ M : ℕ in atTop,∀E : UniformFinite.ExactRestrictedLaw row M,
      ∀hc : 1≤ Uniform07.capacity M,∀i : Fin M,
      Nonempty (ProductKernels05 row (exactNativeGame E hc (sourceLowerPriceCeiling row))
        i (sourceLowerPriceCeiling row) tol) := by
  filter_upwards [eventual_native_positive_product_kernels row (half_pos htol)] with M hPos
  intro E hc i
  let Γ:=exactNativeGame E hc (sourceLowerPriceCeiling row)
  have hzero : |q Γ i 0-sourceProductMarginal row 0|≤ tol ∧
      |duplicate Γ i 0-(sourceProductMarginal row 0)^2|≤ tol := by
    let b:=Uniform07.cutoff row/8
    have ht:=Uniform07.cutoff_pos row
    have hb : 0< b:=by dsimp [b]; positivity
    have hbR : b< sourceLowerPriceCeiling row := by
      have hhalf:=source_seed_cutoff_lt_bidCap row
      have hcap:=(source_auxiliary_floor_guards row).2.1
      dsimp [b]
      linarith
    have hp0 : sourceProductMarginal row 0=0 :=
      source_product_zero_below_quarter row (by positivity)
    have hpb : sourceProductMarginal row b=0 :=
      source_product_zero_below_quarter row (by dsimp [b]; linarith)
    have hq:=(hPos E hc i b ⟨hb,hbR⟩).1
    rw [hpb,sub_zero,abs_of_nonneg (q_nonneg Γ i b)] at hq
    have hS:=exact_native_zero_success_le_eighth E hc i
    have hz:=physical_moment_bounds Γ i (by norm_num : (0:ℝ)≤ 0)
    have hbnds:=physical_moment_bounds Γ i hb.le
    have hid:=success_eq_two_q_sub_duplicate Γ i hb.le
    change success Γ i 0≤ success Γ i b at hS
    simp only [hp0,sub_zero,zero_pow (by norm_num : (2:ℕ)≠0),
      abs_of_nonneg (q_nonneg Γ i 0),abs_of_nonneg hz.1]
    constructor <;> linarith [hz.2.1,hz.2.2.1,hbnds.1]
  have hall (b : ℝ) (hb : b∈Ico (0:ℝ) (sourceLowerPriceCeiling row)) :
      |q Γ i b-sourceProductMarginal row b|≤ tol ∧
      |duplicate Γ i b-(sourceProductMarginal row b)^2|≤ tol := by
    rcases eq_or_lt_of_le hb.1 with hz|hpos
    · subst b
      exact hzero
    · have hh:=hPos E hc i b ⟨hpos,hb.2⟩
      exact ⟨hh.1.trans (by linarith),hh.2.trans (by linarith)⟩
  exact ⟨⟨fun b hb=>(hall b hb).1,fun b hb=>(hall b hb).2⟩⟩

end FCAppendix.Affine.Uniform07Finishing.Concrete05
