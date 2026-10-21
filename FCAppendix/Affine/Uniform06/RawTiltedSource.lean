import FCAppendix.Affine.Uniform06.RawMixedSource
import FCAppendix.Affine.Uniform06.LiteralCenteredArray
import FCAppendix.Affine.Uniform06.LiteralCoarsePath
import FCAppendix.Affine.Uniform06.ExactUntilting

noncomputable section
namespace FCAppendix.Affine.Uniform06.RawTiltedSource

open MeasureTheory ProbabilityTheory Set LowBody
open FCAppendix.ExponentialTilt
open scoped BigOperators
open RawMixedSource ExactUntilting LiteralCoarsePath

section Naturality

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

private theorem preserving_real_integral {μ : Measure α} {ν : Measure β}
    {f : α → β} (hf : MeasurePreserving f μ ν) {g : β → ℝ} (hg : Measurable g) :
    (∫ x, g (f x) ∂μ)=∫ y, g y ∂ν := by
  rw [← hf.map_eq]
  exact (integral_map hf.measurable.aemeasurable hg.aestronglyMeasurable).symm

theorem map_tilted_of_preserving {μ : Measure α} {ν : Measure β}
    {f : α → β} (hf : MeasurePreserving f μ ν)
    {φ : β → ℝ} (hφ : Measurable φ) :
    (μ.tilted (fun x => φ (f x))).map f=ν.tilted φ := by
  have hZ : (∫ x, Real.exp (φ (f x)) ∂μ)=∫ y, Real.exp (φ y) ∂ν :=
    preserving_real_integral hf hφ.exp
  ext s hs
  rw [Measure.map_apply hf.measurable hs,
    tilted_apply_eq_ofReal_integral' _ (hs.preimage hf.measurable),
    tilted_apply_eq_ofReal_integral' _ hs,hZ]
  congr 1
  rw [← integral_indicator (hs.preimage hf.measurable),← integral_indicator hs]
  have hh := preserving_real_integral hf
    ((hφ.exp.div_const (∫ y, Real.exp (φ y) ∂ν)).indicator hs)
  simpa only [Function.comp_def,Set.indicator,mem_preimage] using! hh

theorem tilted_preserving {μ : Measure α} {ν : Measure β}
    {f : α → β} (hf : MeasurePreserving f μ ν)
    {φ : β → ℝ} (hφ : Measurable φ) :
    MeasurePreserving f (μ.tilted (fun x => φ (f x))) (ν.tilted φ) :=
  ⟨hf.measurable,map_tilted_of_preserving hf hφ⟩

theorem cgf_comp_of_preserving {μ : Measure α} {ν : Measure β}
    {f : α → β} (hf : MeasurePreserving f μ ν)
    {X : β → ℝ} (hX : Measurable X) (u : ℝ) :
    cgf (fun x => X (f x)) μ u=cgf X ν u := by
  unfold cgf mgf
  exact congrArg Real.log
    (preserving_real_integral hf (hX.const_mul u).exp)

end Naturality

def tiltedSource (i : Uniform07.Row) (G : Measure (ℝ × ℝ)) (b θ : ℝ) :
    Measure RowRival :=
  (source i G).tilted (fun r => -θ*demand (Uniform07.xi i) b r)

theorem tiltedSource_probability (i : Uniform07.Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] {b : ℝ} (hb : 0 < b) (θ : ℝ) :
    IsProbabilityMeasure (tiltedSource i G b θ) :=
  isProbabilityMeasure_unitInterval_tilted (source i G) (measurable_demand _ _)
    (ae_of_all _ (demand_bounds (Uniform07.xi_pos i) hb)) (-θ)

attribute [local irreducible] RawMixedSource.source MixedLaw.law MixedLaw.physicalLowerLaw

theorem tilted_point_preserving (i : Uniform07.Row) (G : Measure (ℝ × ℝ))
    {b : ℝ} (hb : 0 < b) (θ : ℝ) :
    MeasurePreserving (point (Uniform07.xi i) b) (tiltedSource i G b θ)
      (MixedLaw.tiltedLaw i (MixedLaw.physicalLowerLaw i b G) (-θ)) := by
  have hφ : Measurable (fun p : MixedLaw.Pair => (-θ)*p.1) :=
    measurable_fst.const_mul (-θ)
  have hp := point_preserving i G hb
  have hh := tilted_preserving hp hφ
  simpa only [tiltedSource,MixedLaw.tiltedLaw,point] using! hh

theorem iid_tilted_point_preserving (i : Uniform07.Row) (G : Measure (ℝ × ℝ))
    {b : ℝ} (hb : 0 < b) (θ : ℝ) (N : ℕ) :
    MeasurePreserving (fun ω : Fin N → RowRival => fun j => point (Uniform07.xi i) b (ω j))
      (Measure.pi (fun _ : Fin N => tiltedSource i G b θ))
      (Measure.pi (fun _ : Fin N =>
        MixedLaw.tiltedLaw i (MixedLaw.physicalLowerLaw i b G) (-θ))) := by
  letI : IsFiniteMeasure (tiltedSource i G b θ) := by unfold tiltedSource; infer_instance
  letI : IsFiniteMeasure (MixedLaw.tiltedLaw i (MixedLaw.physicalLowerLaw i b G) (-θ)) := by
    unfold MixedLaw.tiltedLaw
    infer_instance
  refine ⟨measurable_pi_lambda _ (fun j => (measurable_point _ _).comp (measurable_pi_apply j)),?_⟩
  rw [Measure.pi_map_pi (fun _ => (measurable_point (Uniform07.xi i) b).aemeasurable)]
  simp only [(tilted_point_preserving i G hb θ).map_eq]

def integerSign (r : RowRival) : ℤ := if r.1=2 then 1 else if r.1=3 then -1 else 0

theorem measurable_integerSign : Measurable integerSign := by
  unfold integerSign
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    measurable_const (Measurable.ite
      (measurableSet_eq_fun measurable_fst measurable_const) measurable_const measurable_const)

theorem integerSign_cast (r : RowRival) : (integerSign r : ℝ)=sign r := by
  unfold integerSign sign
  split_ifs <;> norm_num

theorem integerSign_point (ξ b : ℝ) (r : RowRival) :
    LiteralCenteredArray.integerSign (point ξ b r)=integerSign r := by
  generalize hr : r.1=k
  fin_cases k <;> norm_num [LiteralCenteredArray.integerSign,point,sign,integerSign,hr,Fin.ext_iff]

def deficit {N : ℕ} (i : Uniform07.Row) (b cap : ℝ) (ω : Fin N → RowRival) : ℝ :=
  cap-iidSum (demand (Uniform07.xi i) b) N ω

def imbalanceSum {N : ℕ} (ω : Fin N → RowRival) : ℤ :=
  MixedProductCharacteristic.integerSum integerSign N ω

theorem measurable_deficit {N : ℕ} (i : Uniform07.Row) (b cap : ℝ) :
    Measurable (deficit (N := N) i b cap) :=
  measurable_const.sub (by
    simpa only [iidSum,MixedProductCharacteristic.continuousSum] using!
      MixedProductCharacteristic.measurable_continuousSum (measurable_demand (Uniform07.xi i) b) N)

theorem measurable_imbalanceSum {N : ℕ} : Measurable (@imbalanceSum N) :=
  MixedProductCharacteristic.measurable_integerSum measurable_integerSign N

theorem imbalanceSum_cast {N : ℕ} (ω : Fin N → RowRival) :
    (imbalanceSum ω : ℝ)=∑ j, sign (ω j) := by
  simp only [imbalanceSum,MixedProductCharacteristic.integerSum,Int.cast_sum,integerSign_cast]

theorem draws_eq_natAbs {N : ℕ} (ω : Fin N → RowRival) :
    draws ω=(imbalanceSum ω).natAbs := by
  have hcast (z : ℤ) : ((z.natAbs : ℕ) : ℝ)=|(z : ℝ)| := by
    cases z with
    | ofNat n => simp
    | negSucc n =>
      simp only [Int.natAbs_negSucc,Int.cast_negSucc,Nat.cast_succ]
      rw [abs_of_nonpos (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
      ring
  have hh := draws_eq_abs ω
  rw [← imbalanceSum_cast,← hcast] at hh
  exact_mod_cast hh

theorem integral_tilted_deficit_test (i : Uniform07.Row) (G : Measure (ℝ × ℝ))
    {b : ℝ} (hb : 0 < b) (θ cap : ℝ) (N : ℕ)
    {F : ℝ × ℤ → ℝ} (hF : Measurable F) :
    (∫ ω : Fin N → RowRival, F (deficit i b cap ω,imbalanceSum ω)
        ∂Measure.pi (fun _ => tiltedSource i G b θ))=
      ∫ p : Fin N → MixedLaw.Pair,
        F (cap-iidSum Prod.fst N p,
          MixedProductCharacteristic.integerSum LiteralCenteredArray.integerSign N p)
          ∂Measure.pi (fun _ => MixedLaw.tiltedLaw i (MixedLaw.physicalLowerLaw i b G) (-θ)) := by
  have htest : Measurable (fun p : Fin N → MixedLaw.Pair =>
      F (cap-iidSum Prod.fst N p,
        MixedProductCharacteristic.integerSum LiteralCenteredArray.integerSign N p)) := by
    apply hF.comp
    refine (measurable_const.sub ?_).prodMk ?_
    · simpa only [iidSum,MixedProductCharacteristic.continuousSum] using!
        MixedProductCharacteristic.measurable_continuousSum measurable_fst N
    · exact MixedProductCharacteristic.measurable_integerSum
        LiteralCenteredArray.measurable_integerSign N
  have hh := preserving_real_integral (iid_tilted_point_preserving i G hb θ N) htest
  simp only [MixedProductCharacteristic.integerSum,integerSign_point] at hh
  simpa only [deficit,imbalanceSum,iidSum,MixedProductCharacteristic.integerSum,
    point] using! hh

theorem source_cost_eq_mixed_cost (i : Uniform07.Row) (G : Measure (ℝ × ℝ))
    {b : ℝ} (hb : 0 < b) (θ cap : ℝ) (N : ℕ) :
    cost (source i G) (demand (Uniform07.xi i) b) θ cap N=
      cost (MixedLaw.law i (MixedLaw.physicalLowerLaw i b G)) Prod.fst θ cap N := by
  unfold cost
  rw [show cgf (demand (Uniform07.xi i) b) (source i G) (-θ)=
      cgf Prod.fst (MixedLaw.law i (MixedLaw.physicalLowerLaw i b G)) (-θ) from
        cgf_comp_of_preserving (point_preserving i G hb) measurable_fst (-θ)]

theorem source_canonical_marginal_untilt (i : Uniform07.Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] (g : LiteralExperiment.GuardData)
    (countMargin : (Fin (m-1) → Fin 4) → ℝ) {b : ℝ} (hb : 0 < b) (θ : ℝ) :
    LiteralExperiment.sourceCanonicalMarginal i m G g countMargin b=
      Real.exp (-cost (source i G) (demand (Uniform07.xi i) b) θ (Uniform07.capacity m) (m-1))*
        ∫ ω : Fin (m-1) → RowRival,
          Real.exp (-θ*deficit i b (Uniform07.capacity m) ω)*
            originalRowMarginal (Uniform07.xi i) (Uniform07.capacity m) g countMargin b ω
              ∂Measure.pi (fun _ => tiltedSource i G b θ) := by
  rw [sourceCanonicalMarginal_eq_integral]
  exact iid_reverse_tilt (source i G) (measurable_demand _ _)
    (ae_of_all _ (demand_bounds (Uniform07.xi_pos i) hb)) θ (Uniform07.capacity m) (m-1) _

theorem source_canonical_duplicate_untilt (i : Uniform07.Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] (g : LiteralExperiment.GuardData)
    (countMargin : (Fin (m-1) → Fin 4) → ℝ) {b : ℝ} (hb : 0 < b) (θ : ℝ) :
    LiteralExperiment.sourceCanonicalDuplicate i m G g countMargin b=
      Real.exp (-cost (source i G) (demand (Uniform07.xi i) b) θ (Uniform07.capacity m) (m-1))*
        ∫ ω : Fin (m-1) → RowRival,
          Real.exp (-θ*deficit i b (Uniform07.capacity m) ω)*
            originalRowDuplicate (Uniform07.xi i) (Uniform07.capacity m) g countMargin b ω
              ∂Measure.pi (fun _ => tiltedSource i G b θ) := by
  rw [sourceCanonicalDuplicate_eq_integral]
  exact iid_reverse_tilt (source i G) (measurable_demand _ _)
    (ae_of_all _ (demand_bounds (Uniform07.xi_pos i) hb)) θ (Uniform07.capacity m) (m-1) _

theorem original_fixed_marks_untilt (i : Uniform07.Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] {b : ℝ} (hb : 0 < b)
    (θ cap markSum : ℝ) (N k : ℕ) (F : (Fin N → RowRival) → ℝ) :
    (∫ ω,F ω ∂Measure.pi (fun _ : Fin N => source i G))=
      Real.exp (-cost (source i G) (demand (Uniform07.xi i) b) θ cap (N+k))*
        Real.exp (-θ*markSum-(k : ℝ)*cgf (demand (Uniform07.xi i) b) (source i G) (-θ))*
          ∫ ω,Real.exp (-θ*deficit i b (cap-markSum) ω)*F ω
            ∂Measure.pi (fun _ : Fin N => tiltedSource i G b θ) :=
  fixed_prefix_reverse_tilt (source i G) (measurable_demand _ _)
    (ae_of_all _ (demand_bounds (Uniform07.xi_pos i) hb)) θ cap markSum N k F

end FCAppendix.Affine.Uniform06.RawTiltedSource
