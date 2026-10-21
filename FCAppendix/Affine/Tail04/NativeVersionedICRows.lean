import FCAppendix.Affine.Tail04.NativeVersionedUpperCounts
import FCAppendix.Affine.Tail04.NativeSourceSuccess
import FCAppendix.Affine.Tail04.OriginalFixedTerminal
import FCAppendix.Game.JointMeasurability

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeVersionedSource
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 OriginalValues CoefficientOne NativeVersionedRows

variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)
  (V : NativeImplementation (NativeSource.input s hs))

def boundedRow (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k) (err : ℝ) (herr : 0 ≤ err) :
    BoundedRow s.scalar (V.toNativeFamilyData.M k) where
  C := context s hs V k
  PL := (data s hs V k hk).PL
  PA := (data s hs V k hk).PA
  PH0 := (data s hs V k hk).PH
  low_value := (data s hs V k hk).low_value
  active_value := (data s hs V k hk).active_value
  low_shape := low_shape s hs V k hk
  active_shape := active_shape s hs V k hk
  upper_shape := upper_shape s hs V k
  upper_bounded := ⟨s.upperMax,by
    apply Measure.ae_compProd_of_ae_ae (measurableSet_Icc.preimage measurable_fst)
    exact s.upper_value_support.mono (fun v hv => Eventually.of_forall (fun _ => hv))⟩
  low_atomless := row_bid_atomless s hs V (lowValue (P := P)) (low_ac s) k
  active_atomless := row_bid_atomless s hs V (activeValue (P := P)) (active_ac s) k
  upper_atomless := row_bid_atomless s hs V s.FH0 (upper_ac s) k
  error := err
  error_nonnegative := herr

lemma bounded_reference_eq (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k)
    (err : ℝ) (herr : 0 ≤ err) :
    (boundedRow s hs V k hk err herr).reference = V.toNativeFamilyData.baseGame k :=
  base_reference_eq s hs V k hk

lemma row_joint_BR (mu : ProbabilityMeasure ℝ) (hmu : (mu : Measure ℝ) ≪ s.valueMeasure)
    (k : ℕ) (i : Fin (V.toNativeFamilyData.M k)) :
    ∀ᵐ x ∂(row mu (V.toNativeFamilyData.game k).σ : Measure (ℝ × JointAction 2)),
      (problem (V.toNativeFamilyData.baseGame k) i).BestResponse x.1 x.2 := by
  have hac : (mu : Measure ℝ) ≪ (V.toNativeFamilyData.game k).F := by
    rw [V.toNativeFamilyData.original_F k,NativeSource.input_original_values s hs]
    exact hmu
  have h := (hac.compProd_left (V.toNativeFamilyData.game k).σ).ae_le
    (ae_bestResponse_compProd (V.toNativeFamilyData.game k) (V.users_optimal k) i)
  filter_upwards [h] with x hx
  intro dev
  rw [← V.toNativeFamilyData.raw_payoff k i x.1 dev,
    ← V.toNativeFamilyData.raw_payoff k i x.1 x.2]
  exact hx dev

lemma low_joint_BR (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k)
    (err : ℝ) (herr : 0 ≤ err) (i : Fin (V.toNativeFamilyData.M k)) :
    ∀ᵐ x ∂((boundedRow s hs V k hk err herr).PL : Measure (ℝ × JointAction 2)),
      (problem (boundedRow s hs V k hk err herr).reference i).BestResponse x.1 x.2 := by
  rw [bounded_reference_eq s hs V k hk err herr]
  exact row_joint_BR s hs V (lowValue (P := P)) (low_ac s) k i

lemma active_joint_BR (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k)
    (err : ℝ) (herr : 0 ≤ err) (i : Fin (V.toNativeFamilyData.M k)) :
    ∀ᵐ x ∂((boundedRow s hs V k hk err herr).PA : Measure (ℝ × JointAction 2)),
      (problem (boundedRow s hs V k hk err herr).reference i).BestResponse x.1 x.2 := by
  rw [bounded_reference_eq s hs V k hk err herr]
  exact row_joint_BR s hs V (activeValue (P := P)) (active_ac s) k i

lemma exists_source_success_error :
    ∃ err : ℕ → ℝ,(∀ k,0 < err k) ∧ Tendsto err atTop (nhds 0) ∧
      ∀ᶠ k in atTop,∀ (i : Fin (V.toNativeFamilyData.M k)) (act : JointAction 2),
        act.bid < s.scalar.R →
        ((problem (V.toNativeFamilyData.baseGame k) i).outcome act).success ≤
          1-s.scalar.rho+err k := by
  obtain ⟨err,hpos,hnull,hevent⟩ := NativeSourceSuccess.exists_success_error s hs V.source
  refine ⟨fun k => err (V.toNativeFamilyData.index k),fun k => hpos _,
    hnull.comp V.toNativeFamilyData.index_tendsto,?_⟩
  exact V.toNativeFamilyData.index_tendsto.eventually hevent

end FCAppendix.Affine.Tail04.NativeVersionedSource
