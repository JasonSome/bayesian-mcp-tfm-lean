import FCAppendix.Affine.Tail04.NativeVersionedICRows

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.Affine.Tail04.NativeVersionedSource
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 OriginalValues CoefficientOne NativeVersionedRows
open Existence.RankEnvelope

variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)
  (V : NativeImplementation (NativeSource.input s hs))

lemma eventually_original_guards (err : ℕ → ℝ) (herr : ∀ k,0 ≤ err k)
    (hnull : Tendsto err atTop (nhds 0)) :
    ∀ᶠ k in atTop,(boundedRow s hs V (k+200) (large s hs V k) (err k) (herr k)).finiteGuards := by
  let N := fun k => V.toNativeFamilyData.M (k+200)
  have hN : Tendsto N atTop atTop := V.toNativeFamilyData.M_tendsto.comp (tendsto_add_atTop_nat 200)
  let q := fun k => rank P.fixedUpperMeasure (N k-1) (marketCapacity (N k)) 2 (P.vA-P.w)
  have hq : Tendsto q atTop (𝓝 1) :=
    (original_fixed_rank_tendsto_one P.fixedUpperMeasure P.fixedUpperMeasure_mass_small (P.vA-P.w)).comp hN
  have hE := (original_fixed_error_tendsto_zero P.fixedUpperMeasure P.fixedUpperMeasure_mass_small
    (P.vA-P.w) s.scalar.R P.M (activeMass P.theta*P.zeta) P.fixedUpperBase_pos
    s.scalar.floor_below_upper.le P.fixedUpperBase_le_tail P.original_tail_weight_bounds
    P.fixedUpperMeasure_tail).comp hN
  have hhidden : Tendsto (fun k => s.scalar.eta*s.scalar.R*(1-2*(1-q k))-
      error (rank P.fixedUpperMeasure (N k-1) (marketCapacity (N k)) 2) (P.vA-P.w) s.scalar.R)
      atTop (𝓝 (s.scalar.eta*s.scalar.R)) := by
    convert! ((tendsto_const_nhds (x:=s.scalar.eta*s.scalar.R)).mul
      ((tendsto_const_nhds (x:=(1:ℝ))).sub
        ((tendsto_const_nhds (x:=(2:ℝ))).mul ((tendsto_const_nhds (x:=(1:ℝ))).sub hq)))).sub hE using 1
    norm_num
  have hslope : Tendsto (fun k => q k-(1-s.scalar.rho+err k)) atTop (𝓝 s.scalar.rho) := by
    convert! hq.sub ((tendsto_const_nhds (x:=1-s.scalar.rho)).add hnull) using 1
    ring
  have hboundary : Tendsto (fun k => (P.vA-P.w-s.scalar.R)*q k-
      (P.vA-P.w)*(1-s.scalar.rho+err k)) atTop
      (𝓝 ((P.vA-P.w)*s.scalar.rho-s.scalar.R)) := by
    convert! ((tendsto_const_nhds (x:=P.vA-P.w-s.scalar.R)).mul hq).sub
      ((tendsto_const_nhds (x:=P.vA-P.w)).mul
        ((tendsto_const_nhds (x:=1-s.scalar.rho)).add hnull)) using 1
    ring
  filter_upwards [hhidden.eventually (Ioi_mem_nhds (mul_pos s.scalar.eta_pos s.scalar.floor_pos)),
    hslope.eventually (Ioi_mem_nhds s.scalar.rho_pos),
    hboundary.eventually (Ioi_mem_nhds (sub_pos.mpr s.scalar.upper_gap_rho))] with k hh hsl hb
  change error (rank P.fixedUpperMeasure (N k-1) (marketCapacity (N k)) 2) (P.vA-P.w) s.scalar.R <
      s.scalar.eta*s.scalar.R*(1-2*(1-q k)) ∧
    1-s.scalar.rho+err k < q k ∧
    (P.vA-P.w)*(1-s.scalar.rho+err k) ≤ (P.vA-P.w-s.scalar.R)*q k
  exact ⟨by linarith,by linarith,by linarith⟩

theorem eventually_original_users : ∀ᶠ k in atTop,UsersOptimal (originalGame s hs V k) := by
  obtain ⟨err,hpos,hnull,hevent⟩ := exists_source_success_error s hs V
  let e := fun k => err (k+200)
  have he0 : ∀ k,0 ≤ e k := fun k => (hpos (k+200)).le
  have henull : Tendsto e atTop (nhds 0) := hnull.comp (tendsto_add_atTop_nat 200)
  filter_upwards [eventually_original_guards s hs V e he0 henull,
    (tendsto_add_atTop_nat 200).eventually hevent] with k hg hsucc
  let d := data s hs V (k+200) (large s hs V k)
  let row := boundedRow s hs V (k+200) (large s hs V k) (e k) (he0 k)
  have hbound : ∀ (i : Fin (V.toNativeFamilyData.M (k+200))) (act : JointAction 2),
      act.bid < s.scalar.R → ((problem row.reference i).outcome act).success ≤ 1-s.scalar.rho+row.error := by
    intro i act ha
    rw [bounded_reference_eq s hs V (k+200) (large s hs V k) (e k) (he0 k)]
    exact hsucc i act ha
  intro i
  apply Measure.ae_ae_of_ae_compProd
    (p := fun x : ℝ × JointAction 2 => (problem (originalGame s hs V k) i).BestResponse x.1 x.2)
  change ∀ᵐ x ∂d.original.F ⊗ₘ d.original.σ,(problem d.original i).BestResponse x.1 x.2
  rw [d.original_joint]
  simp_rw [d.original_problem i]
  exact row.raw_joint_BR_of_bounds (large s hs V k)
    (low_joint_BR s hs V (k+200) (large s hs V k) (e k) (he0 k))
    (active_joint_BR s hs V (k+200) (large s hs V k) (e k) (he0 k)) hbound hg i

end FCAppendix.Affine.Tail04.NativeVersionedSource
