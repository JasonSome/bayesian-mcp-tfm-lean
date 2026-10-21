import FCAppendix.Affine.Tail04.NativeVersionedBands

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeVersionedSource
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 OriginalValues CoefficientOne NativeVersionedRows
open Existence.RankEnvelope
open scoped BigOperators

variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)
  (V : NativeImplementation (NativeSource.input s hs))

lemma upper_count_expect (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k)
    (v : ℝ) (hv : P.vA-P.w ≤ v) (f : Fin 3 → ℝ) :
    (conditionalTypeCountLaw (data s hs V k hk).original (by omega) v).expect f =
      (1-rank P.fixedUpperMeasure (V.toNativeFamilyData.M k-1)
        (marketCapacity (V.toNativeFamilyData.M k)) 2 v)*f 0+
      rank P.fixedUpperMeasure (V.toNativeFamilyData.M k-1)
        (marketCapacity (V.toNativeFamilyData.M k)) 2 v*f 1 := by
  rw [conditionalTypeCountLaw_expect,(data s hs V k hk).upper_kernel v hv]
  change (∑ i : Fin (V.toNativeFamilyData.M k),
    ∫ act,((problem (data s hs V k hk).original i).outcome act).expect f
      ∂Measure.dirac (upperAction (P.originalFixedUpperBid (V.toNativeFamilyData.M k) s.scalar.R) v)) /
      (V.toNativeFamilyData.M k : ℝ) = _
  have hc := capacity_bounds (V.toNativeFamilyData.M k) hk
  have hterm (i : Fin (V.toNativeFamilyData.M k)) :
      (∫ act,((problem (data s hs V k hk).original i).outcome act).expect f
        ∂Measure.dirac (upperAction
          (P.originalFixedUpperBid (V.toNativeFamilyData.M k) s.scalar.R) v)) =
      (1-rank P.fixedUpperMeasure (V.toNativeFamilyData.M k-1)
        (marketCapacity (V.toNativeFamilyData.M k)) 2 v)*f 0+
      rank P.fixedUpperMeasure (V.toNativeFamilyData.M k-1)
        (marketCapacity (V.toNativeFamilyData.M k)) 2 v*f 1 := by
    rw [integral_dirac,(data s hs V k hk).original_problem i]
    exact native_original_upper_count_expect _ P.fixedUpperMeasure (by omega) hc.2.2.1 hc.2.2.2
      (P.fixedUpperMeasure_mass_small.trans (by norm_num)) (P.vA-P.w) s.scalar.R
      s.scalar.floor_pos s.scalar.floor_below_upper P.fixedUpperMeasure_support
      (P.originalFixedGame_mean hk (context s hs V k) s.scalar.U s.scalar.R
        s.scalar.floor_pos s.scalar.floor_below_upper s.scalar.cap_below_floor
        (data s hs V k hk).PL (data s hs V k hk).PA
        ((low_shape s hs V k hk).mono (fun _ h => h.1))
        ((active_shape s hs V k hk).mono (fun _ h => h.1))
        s.scalar.eta s.scalar.eta_pos.le s.scalar.eta_lt_one) i v hv f
  simp_rw [hterm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hmR : (V.toNativeFamilyData.M k : ℝ) ≠ 0 := by exact_mod_cast (by omega : V.toNativeFamilyData.M k ≠ 0)
  field_simp

lemma upper_expect_limit (v : ℝ) (hv : P.vA-P.w ≤ v) (f : Fin 3 → ℝ) :
    Tendsto (fun k => (conditionalTypeCountLaw (originalGame s hs V k)
      (by have := large s hs V k;omega) v).expect f) atTop (𝓝 (f 1)) := by
  have hM := V.toNativeFamilyData.M_tendsto.comp (tendsto_add_atTop_nat 200)
  have hq := (original_fixed_rank_tendsto_one P.fixedUpperMeasure
    P.fixedUpperMeasure_mass_small v).comp hM
  have hlim := ((tendsto_const_nhds (x := (1:ℝ))).sub hq).mul_const (f 0) |>.add (hq.mul_const (f 1))
  simp only [sub_self,zero_mul,one_mul,zero_add] at hlim
  convert! hlim using 1
  funext k
  exact upper_count_expect s hs V (k+200) (large s hs V k) v hv f

lemma upper_count_limit (v : ℝ) (hv : P.vA-P.w ≤ v) (r : Fin 3) :
    Tendsto (fun k => (conditionalTypeCountLaw (originalGame s hs V k)
      (by have := large s hs V k;omega) v).mass r) atTop
      (𝓝 ((FiniteLaw.dirac (1:Fin 3)).mass r)) := by
  classical
  have h := upper_expect_limit s hs V v hv (fun q => if q=r then 1 else 0)
  simp only [FiniteLaw.expect_singleton] at h
  have he : (if (1:Fin 3)=r then (1:ℝ) else 0) = (FiniteLaw.dirac (1:Fin 3)).mass r := by
    by_cases hr : r=1
    · simp [FiniteLaw.dirac,hr]
    · simp [FiniteLaw.dirac,hr,Ne.symm hr]
  rw [he] at h
  exact h

end FCAppendix.Affine.Tail04.NativeVersionedSource
