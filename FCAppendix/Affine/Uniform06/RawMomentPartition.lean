import FCAppendix.Affine.Uniform06.RawPathRootReplacement
import FCAppendix.Affine.Uniform06.GuardedSampledMoments

noncomputable section
namespace FCAppendix.Affine.Uniform06.RawMomentPartition

open Set MeasureTheory LowBody
open scoped BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open LiteralCoarsePath LiteralKernelIdentity LiteralGuardRare GuardedSampledMoments
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open RawPathAdapter RawPathRootReplacement ZeroWeightFocal PathNumerator
open FiniteSampledLaplace FiniteMarkedExchangeability SampledCellDomination

variable {N : ℕ} [Nonempty (Fin N)]

def strictPower (q : ℕ) (D : ℝ) : ℝ := if 0< D then D^q else 0

lemma strictPower_nonneg (q : ℕ) (D : ℝ) : 0 ≤ strictPower q D := by
  unfold strictPower
  split_ifs with h
  · exact pow_nonneg h.le q
  · rfl

def literalMoment (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) : ℝ :=
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin := cm (fun j => (ω j).1)}
  Real.exp (-θ*((c:ℝ)-sumX (demand (xi i) b) ω))*branchWeight (xi i) g' T B*
    (pathLaw (weights (xi i) g' T B) (imbalance T) ∅).expect
      (fun p => strictPower q (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0))

def literalTest (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (F : ℝ → ℝ)
    (ω : Fin N → RowRival) : ℝ :=
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin := cm (fun j => (ω j).1)}
  Real.exp (-θ*((c:ℝ)-sumX (demand (xi i) b) ω))*branchWeight (xi i) g' T B*
    (pathLaw (weights (xi i) g' T B) (imbalance T) ∅).expect
      (fun p => F (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0))

theorem measurable_focalDeficit {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (ξ : ℝ) (T : PureTemplate ι)
    (B : Ω → ι → ℝ) (hB : ∀ j,Measurable (fun ω => B ω j))
    (E : Finset ι) (j : ι) :
    Measurable (fun ω => focalDeficit ξ T (B ω) E j) := by
  unfold focalDeficit remainingDemand
  apply measurable_const.sub
  apply Finset.measurable_sum
  intro k _
  by_cases hk : k ∈ insert j E
  · simpa only [if_pos hk] using
      (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  · simp only [if_neg hk]
    unfold exposure
    fun_prop

theorem measurable_strictPower (q : ℕ) : Measurable (strictPower q) := by
  unfold strictPower
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (measurable_id.pow_const q) measurable_const

omit [Nonempty (Fin N)] in

theorem measurable_literalTest (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (F : ℝ → ℝ)
    (hF : Measurable F) : Measurable (literalTest i c g cm b θ F) := by
  classical
  have hsum : Measurable (fun ω : Fin N → RowRival =>
      sumX (demand (xi i) b) ω) := by
    unfold sumX
    exact Finset.measurable_sum _ (fun j _ =>
      (measurable_demand (xi i) b).comp (measurable_pi_apply j))
  have hcost : Measurable (fun ω : Fin N → RowRival =>
      Real.exp (-θ*((c:ℝ)-sumX (demand (xi i) b) ω))) :=
    (measurable_const.mul (measurable_const.sub hsum)).exp
  apply LiteralCoarseMeasurable.measurable_pattern_choice
    (fun kind ω =>
      Real.exp (-θ*((c:ℝ)-sumX (demand (xi i) b) ω))*
      branchWeight (xi i) {g with countMargin := cm kind}
        (patternTemplate c kind) (rowBids b ω)*
      (pathLaw (weights (xi i) {g with countMargin := cm kind}
        (patternTemplate c kind) (rowBids b ω))
        (imbalance (patternTemplate c kind)) ∅).expect
        (fun p => F (focalDeficit (xi i) (patternTemplate c kind)
          (rowBids b ω) (finalSet (imbalance (patternTemplate c kind)) ∅ p) 0)))
  intro kind
  let T := patternTemplate c kind
  let g' := {g with countMargin := cm kind}
  have hB := LiteralCoarseMeasurable.measurable_raw_rowBids N b
  have hα : Measurable (fun ω : Fin N → RowRival =>
      branchWeight (xi i) g' T (rowBids b ω)) := by
    by_cases he : T.residual₀=T.residual₁
    · simpa only [branchWeight,if_pos he] using
        (measurable_const : Measurable (fun _ : Fin N → RowRival => (1 : ℝ)))
    · simpa only [branchWeight,if_neg he] using
        LiteralCoarseMeasurable.measurable_guard (xi i) g' T (rowBids b) hB
  apply (hcost.mul hα).mul
  unfold FCAppendix.FiniteLaw.expect
  apply Finset.measurable_sum
  intro p _
  exact (LiteralCoarseMeasurable.measurable_path_mass
    (fun ω => weights (xi i) g' T (rowBids b ω))
    (LiteralCoarseMeasurable.measurable_weights (xi i) g' T (rowBids b) hB)
    (imbalance T) ∅ p).mul
      (hF.comp (measurable_focalDeficit (xi i) T (rowBids b) hB _ 0))

omit [Nonempty (Fin N)] in
theorem measurable_literalMoment (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) :
    Measurable (literalMoment i c g cm b θ q) := by
  convert! measurable_literalTest i c g cm b θ (strictPower q) (measurable_strictPower q) using 1

def reducedMoment (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) : ℝ :=
  if imbalanceSum ω=0 then
    sampledRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
      (rawWeight_bounds (xi i) g) c θ 0 q 0 ω
  else rawGuard (xi i) g c cm b ω*
    safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
      (rawWeight_bounds (xi i) g) c θ (imbalanceSum ω) q (imbalanceSum ω).natAbs ω

def cellSum (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) : ℝ :=
  sampledRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
    (rawWeight_bounds (xi i) g) c θ 0 q 0 ω+
  ∑ k ∈ Finset.range N,rawGuard (xi i) g c cm b ω*
    (safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
      (rawWeight_bounds (xi i) g) c θ ((k+1:ℕ):ℤ) q (k+1) ω+
     safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
      (rawWeight_bounds (xi i) g) c θ (-((k+1:ℕ):ℤ)) q (k+1) ω)

omit [Nonempty (Fin N)] in
lemma imbalance_zero_iff_equal (c : ℕ) (ω : Fin N → RowRival) (hc : ValidCounts c ω) :
    imbalanceSum ω=0 ↔
      (patternTemplate c (fun j => (ω j).1)).residual₀=
        (patternTemplate c (fun j => (ω j).1)).residual₁ := by
  have hh := literal_imbalance_eq c ω hc
  have he : ∀ T : PureTemplate (Fin (N+1)),imbalance T=0 ↔ T.residual₀=T.residual₁ := by
    intro T
    unfold imbalance small
    omega
  rw [← he,hh,Int.natAbs_eq_zero]

lemma expect_eq_of_support {Ω : Type*} [Fintype Ω] (P : FCAppendix.FiniteLaw Ω)
    {F H : Ω → ℝ} (h : ∀ x,0< P.mass x → F x=H x) : P.expect F=P.expect H := by
  apply le_antisymm
  · exact expect_le_of_support P F H (fun x hx => (h x hx).le)
  · exact expect_le_of_support P H F (fun x hx => (h x hx).ge)

lemma sampledRow_cell_zero (X h w : RowRival → ℝ)
    (hw : ∀ x,w x ∈ Icc (0:ℝ) 1) (cap θ : ℝ) (y : ℤ) (q k : ℕ)
    (ω : Fin N → RowRival) (hy : y ≠ imbalanceSum ω) :
    sampledRow X h w integerSign hw cap θ y q k ω=0 := by
  have hy' : sumY integerSign ω ≠ y := Ne.symm hy
  simp only [sampledRow,tupleTest,hy',false_and,if_false,FCAppendix.FiniteLaw.expect_zero]

lemma safeRow_cell_zero (X h w : RowRival → ℝ)
    (hw : ∀ x,w x ∈ Icc (0:ℝ) 1) (cap θ : ℝ) (y : ℤ) (q k : ℕ)
    (ω : Fin N → RowRival) (hy : y ≠ imbalanceSum ω) :
    safeRow X h w integerSign hw cap θ y q k ω=0 := by
  unfold safeRow
  split_ifs
  · exact sampledRow_cell_zero X h w hw cap θ y q k ω hy
  · rfl

theorem literalMoment_eq_reducedMoment (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (θ : ℝ) (q : ℕ) (hε : 0< g.margin) (hM : 0< g.population)
    (hr : 0< g.requiredDemand) (ω : Fin N → RowRival) (hc : ValidCounts c ω) :
    literalMoment i c g cm b θ q ω=reducedMoment i c g cm b θ q ω := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin := cm (fun j => (ω j).1)}
  let k := (imbalanceSum ω).natAbs
  have himb : imbalance T=k := literal_imbalance_eq c ω hc
  have hY : sumY integerSign ω=imbalanceSum ω := rfl
  by_cases hy : imbalanceSum ω=0
  · have he : T.residual₀=T.residual₁ := (imbalance_zero_iff_equal c ω hc).mp hy
    have hk0 : imbalance T=0 := himb.trans (Int.natAbs_eq_zero.mpr hy)
    have hD : focalDeficit (xi i) T B ∅ 0=(c:ℝ)-sumX (demand (xi i) b) ω := by
      have hh := literal_balanced_deficit_eq i c hb ω hc
      change (small T:ℝ)+(imbalance T:ℝ)/2-remainingDemand (xi i) B {0} (B 0)=_ at hh
      simp only [hk0,Nat.cast_zero,zero_div,add_zero] at hh
      exact hh
    change Real.exp (-θ*((c:ℝ)-sumX (demand (xi i) b) ω))*branchWeight (xi i) g' T B*
      (pathLaw (weights (xi i) g' T B) (imbalance T) ∅).expect
        (fun p => strictPower q (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0))=_
    rw [hk0]
    simp only [branchWeight,if_pos he,pathLaw,FCAppendix.FiniteLaw.expect_dirac,finalSet,hD,mul_one]
    simp only [reducedMoment,sampledRow,FCAppendix.FiniteLaw.expect_dirac,
      pathLaw,tupleTest,hY,hy,Finset.univ_eq_empty,Finset.sum_empty,sub_zero,true_and,strictPower]
    split_ifs <;> simp_all
  · have he : T.residual₀ ≠ T.residual₁ :=
      fun h => hy ((imbalance_zero_iff_equal c ω hc).mpr h)
    by_cases hα : rawGuard (xi i) g c cm b ω=0
    · have hguard : guardAlpha (xi i) g' T B=0 := hα
      change Real.exp (-θ*((c:ℝ)-sumX (demand (xi i) b) ω))*branchWeight (xi i) g' T B*
        (pathLaw (weights (xi i) g' T B) (imbalance T) ∅).expect
          (fun p => strictPower q (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0))=_
      simp only [branchWeight,if_neg he,hguard,mul_zero,zero_mul,
        reducedMoment,if_neg hy,hα]
    · have hαp : 0< guardAlpha (xi i) g' T B :=
        lt_of_le_of_ne (rawGuard_bounds (xi i) g c cm b ω).1 (Ne.symm hα)
      have hWfull := SourceGuardGeometry.positive_guard_weight g' T B hε hM hαp
      have hW : (k:ℝ)< totalWeight
          (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) := by
        rw [literal_weights_eq_lift (xi i) g' c b hbL hr ω,lift_total,himb] at hWfull
        have hh := mul_pos hε hM
        change (k:ℝ)+g.margin*g.population < totalWeight
          (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) at hWfull
        linarith
      have hequiv := actual_rival_path_transport (xi i) g' c b hbL hr ω k hW
        (fun p => strictPower q (focalDeficit (xi i) T B (finalSet k ∅ p) 0))
      have hpoint : (pathLaw (rowWeights (rawWeight (xi i) g)
          (rawWeight_bounds (xi i) g) ω) k ∅).expect
          (fun p => strictPower q (focalDeficit (xi i) T B (finalSet k ∅ (liftPath k p)) 0))=
          (pathLaw (rowWeights (rawWeight (xi i) g)
            (rawWeight_bounds (xi i) g) ω) k ∅).expect
            (fun p => strictPower q (selectedDeficit i c b ω k p)) := by
        apply expect_eq_of_support
        intro p hp
        have hsel := selected_deficit_identity i c g hb ω hc k rfl hW p hp
        have hmask := masked_demand_eq (ξ:=xi i) T B (liftSet (finalSet k ∅ p)) 0 hb
          (rowBids_outside c b ω)
        have hf : focalDeficit (xi i) T B (finalSet k ∅ (liftPath k p)) 0=
            selectedDeficit i c b ω k p := by
          rw [show (∅:Finset (Fin (N+1)))=liftSet (∅:Finset (Fin N)) by simp [liftSet],
            finalSet_lift]
          change (small T:ℝ)-remainingDemand (xi i) (maskedBids T B (liftSet (finalSet k ∅ p)))
            {0} b=selectedDeficit i c b ω k p at hsel
          rw [hmask] at hsel
          convert! hsel using 1
        rw [hf]
      have htest : sampledRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g)
          integerSign (rawWeight_bounds (xi i) g) c θ (imbalanceSum ω) q k ω=
          Real.exp (-θ*((c:ℝ)-sumX (demand (xi i) b) ω))*
            (pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) k ∅).expect
              (fun p => strictPower q (selectedDeficit i c b ω k p)) := by
        rw [← FCAppendix.FiniteLaw.expect_const_mul]
        apply FCAppendix.FiniteLaw.expect_congr
        intro p
        simp only [tupleTest,hY,true_and,strictPower,selectedDeficit]
        split_ifs <;> simp
      have hequiv' : (pathLaw (weights (xi i) g' T B) k ∅).expect
          (fun p => strictPower q (focalDeficit (xi i) T B (finalSet k ∅ p) 0))=
          (pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) k ∅).expect
          (fun p => strictPower q (focalDeficit (xi i) T B (finalSet k ∅ (liftPath k p)) 0)) := by
        convert! hequiv using 1
      change Real.exp (-θ*((c:ℝ)-sumX (demand (xi i) b) ω))*branchWeight (xi i) g' T B*
        (pathLaw (weights (xi i) g' T B) (imbalance T) ∅).expect
          (fun p => strictPower q (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0))=_
      rw [himb]
      have hguard : guardAlpha (xi i) g' T B=rawGuard (xi i) g c cm b ω := rfl
      simp only [reducedMoment,if_neg hy,branchWeight,if_neg he,safeRow]
      rw [hguard,hequiv',hpoint,htest]
      have hW' : ((imbalanceSum ω).natAbs:ℝ)<totalWeight
        (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) := hW
      rw [if_pos hW']
      ring

lemma signed_cell_sum (F : ℤ → ℕ → ℝ) (y : ℤ) (N : ℕ)
    (hsupport : ∀ z k,z≠y → F z k=0) (hy : y.natAbs≤ N) :
    F 0 0+∑ k ∈ Finset.range N,(F ((k+1:ℕ):ℤ) (k+1)+F (-((k+1:ℕ):ℤ)) (k+1))=
      F y y.natAbs := by
  classical
  cases y with
  | ofNat z =>
    change ∀ z' k,z'≠(z:ℤ) → F z' k=0 at hsupport
    change z≤N at hy
    change F 0 0+∑ k ∈ Finset.range N,(F ((k+1:ℕ):ℤ) (k+1)+F (-((k+1:ℕ):ℤ)) (k+1))=F (z:ℤ) z
    cases z with
    | zero =>
      have hp : ∀ k : ℕ,F ((k+1:ℕ):ℤ) (k+1)=0 := fun k => hsupport _ _ (by omega)
      have hm : ∀ k : ℕ,F (-((k+1:ℕ):ℤ)) (k+1)=0 := fun k => hsupport _ _ (by omega)
      simp only [hp,hm,Finset.sum_const_zero,add_zero,Nat.cast_zero]
    | succ j =>
      have hj : j∈Finset.range N := by simp only [Finset.mem_range]; omega
      have hz := hsupport 0 0 (by omega)
      have hp : (∑ k ∈ Finset.range N,F ((k+1:ℕ):ℤ) (k+1))=F ((j+1:ℕ):ℤ) (j+1) := by
        apply Finset.sum_eq_single j
        · intro k hk hkj
          exact hsupport _ _ (by omega)
        · intro hn
          exact (hn hj).elim
      have hm : (∑ k ∈ Finset.range N,F (-((k+1:ℕ):ℤ)) (k+1))=0 := by
        apply Finset.sum_eq_zero
        intro k hk
        exact hsupport _ _ (by omega)
      rw [Finset.sum_add_distrib,hz,hp,hm]
      simp only [zero_add,add_zero]
  | negSucc j =>
    have hj : j∈Finset.range N := by simp only [Finset.mem_range]; simpa using hy
    have hz := hsupport 0 0 (by omega)
    have hp : (∑ k ∈ Finset.range N,F ((k+1:ℕ):ℤ) (k+1))=0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact hsupport _ _ (by omega)
    have hm : (∑ k ∈ Finset.range N,F (-((k+1:ℕ):ℤ)) (k+1))=F (-((j+1:ℕ):ℤ)) (j+1) := by
      apply Finset.sum_eq_single j
      · intro k hk hkj
        exact hsupport _ _ (by omega)
      · intro hn
        exact (hn hj).elim
    rw [Finset.sum_add_distrib,hz,hp,hm]
    simp only [zero_add,Int.natAbs_negSucc]
    rfl

theorem reducedMoment_eq_cellSum (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) :
    reducedMoment i c g cm b θ q ω=cellSum i c g cm b θ q ω := by
  let F : ℤ → ℕ → ℝ := fun y k => if y=0 then
    sampledRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
      (rawWeight_bounds (xi i) g) c θ y q k ω
    else rawGuard (xi i) g c cm b ω*
      safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
        (rawWeight_bounds (xi i) g) c θ y q k ω
  have hh := signed_cell_sum F (imbalanceSum ω) N (by
    intro y k hy
    dsimp only [F]
    split_ifs
    · exact sampledRow_cell_zero _ _ _ _ _ _ _ _ _ _ hy
    · rw [safeRow_cell_zero _ _ _ _ _ _ _ _ _ _ hy,mul_zero])
    (by rw [← draws_eq_natAbs]; exact draws_le ω)
  have hpos (k : ℕ) : ((k+1:ℕ):ℤ)≠0 := by omega
  have hneg (k : ℕ) : (-((k+1:ℕ):ℤ))≠0 := by omega
  simp only [F,if_pos rfl,if_neg (hpos _),if_neg (hneg _),← mul_add] at hh
  change cellSum i c g cm b θ q ω=_ at hh
  rw [hh]
  unfold reducedMoment
  split_ifs with hy
  · simp only [hy,Int.natAbs_zero]
  · rfl

theorem literalMoment_eq_cellSum (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (θ : ℝ) (q : ℕ) (hε : 0< g.margin) (hM : 0< g.population)
    (hr : 0< g.requiredDemand) (ω : Fin N → RowRival) (hc : ValidCounts c ω) :
    literalMoment i c g cm b θ q ω=cellSum i c g cm b θ q ω :=
  (literalMoment_eq_reducedMoment i c g cm hb hbL θ q hε hM hr ω hc).trans
    (reducedMoment_eq_cellSum i c g cm b θ q ω)

lemma measurable_cellSum (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) :
    Measurable (cellSum i c g cm b θ q) := by
  apply (measurable_sampledRow (measurable_demand (xi i) b) (measurable_rawH (xi i) b)
    (measurable_rawWeight (xi i) g) measurable_integerSign _ _ _ _ _ _).add
  apply Finset.measurable_sum
  intro k hk
  exact (measurable_rawGuard (xi i) g c cm b).mul
    ((measurable_safeRow (measurable_demand (xi i) b) (measurable_rawH (xi i) b)
      (measurable_rawWeight (xi i) g) measurable_integerSign _ _ _ _ _ _).add
     (measurable_safeRow (measurable_demand (xi i) b) (measurable_rawH (xi i) b)
      (measurable_rawWeight (xi i) g) measurable_integerSign _ _ _ _ _ _))

lemma cellSum_nonneg (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) :
    0≤ cellSum i c g cm b θ q ω := by
  unfold cellSum
  apply add_nonneg
  · exact expect_nonneg _ _ (fun p => tupleTest_nonneg _ _ _ _ _ _ _ _ _)
  · apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (rawGuard_bounds _ _ _ _ _ _).1
      (add_nonneg (safeRow_nonneg _ _ _ _ _ _ _ _ _ _ _) (safeRow_nonneg _ _ _ _ _ _ _ _ _ _ _))

lemma cellSum_polynomial (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b θ : ℝ} (hb : 0< b) (hθ : 0≤θ)
    (q : ℕ) (hN : 0< N) (hc : (c:ℝ)≤ N) (ω : Fin N → RowRival)
    (hh : ∀ j,0≤ rawH (xi i) b (ω j)) :
    cellSum i c g cm b θ q ω ∈ Icc (0:ℝ) ((N:ℝ)^q) := by
  rw [← reducedMoment_eq_cellSum]
  unfold reducedMoment
  split_ifs
  · exact (row_polynomial_bounds _ _ _ _ _ _ _ _ _ _ ω hN
      (fun j => (demand_bounds (xi_pos i) hb (ω j)).1) hh hc hθ).1
  · have hp := (row_polynomial_bounds (demand (xi i) b) (rawH (xi i) b)
      (rawWeight (xi i) g) integerSign (rawWeight_bounds (xi i) g) c θ
      (imbalanceSum ω) q (imbalanceSum ω).natAbs ω hN
      (fun j => (demand_bounds (xi_pos i) hb (ω j)).1) hh hc hθ).1
    have hs0 := safeRow_nonneg (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g)
      integerSign (rawWeight_bounds (xi i) g) c θ (imbalanceSum ω) q (imbalanceSum ω).natAbs ω
    have hs1 := (SampledSafeLimit.safe_le_sampled (demand (xi i) b) (rawH (xi i) b)
      (rawWeight (xi i) g) integerSign (rawWeight_bounds (xi i) g) c θ
      (imbalanceSum ω) q (imbalanceSum ω).natAbs ω).trans hp.2
    have ha := rawGuard_bounds (xi i) g c cm b ω
    exact ⟨mul_nonneg ha.1 hs0,(mul_le_mul_of_nonneg_right ha.2 hs0).trans
      (by simpa only [one_mul] using hs1)⟩

lemma safeCell_zero_outside (i : Row) (μ : Measure RowRival) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q k : ℕ) (hk : N≤ k) :
    safeCell i μ N c g cm b θ ((k+1:ℕ):ℤ) (k+1) q=0 ∧
    safeCell i μ N c g cm b θ (-((k+1:ℕ):ℤ)) (k+1) q=0 := by
  have hzero (y : ℤ) (hy : N< y.natAbs) : safeCell i μ N c g cm b θ y (k+1) q=0 := by
    unfold safeCell
    have he : (fun ω : Fin N → RowRival => rawGuard (xi i) g c cm b ω*
        safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
          (rawWeight_bounds (xi i) g) c θ y q (k+1) ω)=fun _ => 0 := by
      funext ω
      have hn : y≠imbalanceSum ω := by
        intro h
        have hb : (imbalanceSum ω).natAbs≤ N := by rw [← draws_eq_natAbs]; exact draws_le ω
        rw [h] at hy
        omega
      rw [safeRow_cell_zero _ _ _ _ _ _ _ _ _ _ hn,mul_zero]
    rw [he,integral_zero,mul_zero]
  exact ⟨hzero _ (by simpa only [Int.natAbs_natCast] using Nat.lt_succ_of_le hk),
    hzero _ (by simpa only [Int.natAbs_neg,Int.natAbs_natCast] using Nat.lt_succ_of_le hk)⟩

theorem normalized_integral_cellSum (i : Row) (μ : Measure RowRival) [IsProbabilityMeasure μ]
    (c : ℕ) (g : GuardData) (cm : (Fin N → Fin 4) → ℝ) {b θ : ℝ}
    (hb : 0< b) (hθ : 0≤θ) (q : ℕ) (hN : 0< N) (hc : (c:ℝ)≤ N)
    (hh : ∀ᵐ r ∂μ,0≤ rawH (xi i) b r) :
    (N:ℝ)*(∫ ω : Fin N → RowRival,cellSum i c g cm b θ q ω
        ∂Measure.pi (fun _ : Fin N => μ))=
      zeroCell i μ N c g b θ q+
        ∑' k : ℕ,(safeCell i μ N c g cm b θ ((k+1:ℕ):ℤ) (k+1) q+
          safeCell i μ N c g cm b θ (-((k+1:ℕ):ℤ)) (k+1) q) := by
  let P := Measure.pi (fun _ : Fin N => μ)
  let Z : (Fin N → RowRival) → ℝ := sampledRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g)
    integerSign (rawWeight_bounds (xi i) g) c θ 0 q 0
  let F : ℤ → ℕ → (Fin N → RowRival) → ℝ := fun y k => fun ω : Fin N → RowRival => rawGuard (xi i) g c cm b ω*
    safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g)
      integerSign (rawWeight_bounds (xi i) g) c θ y q k ω
  have hpositive : ∀ᵐ r ∂μ,0≤ demand (xi i) b r ∧ 0≤ rawH (xi i) b r :=
    hh.mono fun r hr => ⟨(demand_bounds (xi_pos i) hb r).1,hr⟩
  have hZ : Integrable Z P := Integrable.of_mem_Icc 0 ((N:ℝ)^q)
    (measurable_sampledRow (measurable_demand (xi i) b) (measurable_rawH (xi i) b)
      (measurable_rawWeight (xi i) g) measurable_integerSign _ _ _ _ _ _).aemeasurable
    ((SampledSafeLimit.polynomial_sampled_ae μ hN _ _ _ _ _ hpositive hc hθ 0 q 0).mono
      fun _ hx => hx.1)
  have hF (y : ℤ) (k : ℕ) : Integrable (F y k) P := by
    apply Integrable.of_mem_Icc 0 ((N:ℝ)^q)
      ((measurable_rawGuard (xi i) g c cm b).mul
        (measurable_safeRow (measurable_demand (xi i) b) (measurable_rawH (xi i) b)
          (measurable_rawWeight (xi i) g) measurable_integerSign _ _ _ _ _ _)).aemeasurable
    filter_upwards [SampledSafeLimit.polynomial_sampled_ae μ hN _ _ _ _ _ hpositive hc hθ y q k]
      with ω hω
    have ha := rawGuard_bounds (xi i) g c cm b ω
    exact ⟨mul_nonneg ha.1 hω.2.1,(mul_le_mul_of_nonneg_right ha.2 hω.2.1).trans
      (by simpa only [one_mul] using hω.2.2)⟩
  have hfinite : (∫ ω : Fin N → RowRival,cellSum i c g cm b θ q ω ∂P)=
      (∫ ω,Z ω ∂P)+∑ k ∈ Finset.range N,
        ((∫ ω,F ((k+1:ℕ):ℤ) (k+1) ω ∂P)+(∫ ω,F (-((k+1:ℕ):ℤ)) (k+1) ω ∂P)) := by
    simp only [cellSum,mul_add]
    change (∫ ω : Fin N → RowRival,Z ω+∑ k ∈ Finset.range N,
      (F ((k+1:ℕ):ℤ) (k+1) ω+F (-((k+1:ℕ):ℤ)) (k+1) ω) ∂P)=_
    have hi (k : ℕ) (_hk : k∈Finset.range N) : Integrable
        (fun ω => F ((k+1:ℕ):ℤ) (k+1) ω+F (-((k+1:ℕ):ℤ)) (k+1) ω) P :=
      (hF _ _).add (hF _ _)
    rw [integral_add hZ (integrable_finsetSum _ hi),integral_finsetSum _ hi]
    simp_rw [integral_add (hF _ _) (hF _ _)]
  let a := fun k => safeCell i μ N c g cm b θ ((k+1:ℕ):ℤ) (k+1) q+
    safeCell i μ N c g cm b θ (-((k+1:ℕ):ℤ)) (k+1) q
  have hasum : HasSum a (∑ k ∈ Finset.range N,a k) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hkn : N≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
    have hz := safeCell_zero_outside (N:=N) i μ c g cm b θ q k hkn
    dsimp only [a]
    rw [hz.1,hz.2,zero_add]
  rw [hasum.tsum_eq,hfinite,mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [a,safeCell,F,P,mul_add]

end FCAppendix.Affine.Uniform06.RawMomentPartition
