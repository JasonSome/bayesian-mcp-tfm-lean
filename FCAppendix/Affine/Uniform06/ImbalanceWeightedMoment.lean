import FCAppendix.Affine.Uniform06.RawMomentPartition

noncomputable section
namespace FCAppendix.Affine.Uniform06.ImbalanceWeightedMoment

open MeasureTheory Set Filter LowBody
open scoped Topology BigOperators
open Uniform07 RawMixedSource RawTiltedSource RawMarkedLaplace LiteralExperiment
open RawMomentPartition GuardedSampledMoments LiteralGuardRare
open FiniteSampledLaplace SampledCellDomination SampledSafeLimit

lemma finite_weighted_geometric_identity (Q : ℝ) (N : ℕ) :
    (1-Q)^2*(∑ k ∈ Finset.range N,((k+1:ℕ):ℝ)*Q^(k+1))=
      Q-Q^(N+1)*(((N+1:ℕ):ℝ)- (N:ℝ)*Q) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,mul_add,ih]
    push_cast
    simp only [pow_succ]
    ring

lemma finite_weighted_geometric_le {Q : ℝ} (hQ0 : 0≤ Q) (hQ1 : Q<1) (N : ℕ) :
    (∑ k ∈ Finset.range N,((k+1:ℕ):ℝ)*Q^(k+1))≤ Q/(1-Q)^2 := by
  have hd : 0<(1-Q)^2 := sq_pos_of_pos (sub_pos.mpr hQ1)
  apply (le_div_iff₀ hd).mpr
  rw [mul_comm,finite_weighted_geometric_identity]
  have hm : 0≤((N+1:ℕ):ℝ)-(N:ℝ)*Q := by
    have h := mul_le_mul_of_nonneg_left hQ1.le (Nat.cast_nonneg N : (0:ℝ)≤ N)
    push_cast
    nlinarith
  have hz := mul_nonneg (pow_nonneg hQ0 (N+1)) hm
  linarith

lemma signed_weighted_cell_sum (F : ℤ → ℕ → ℝ) (y : ℤ) (N : ℕ)
    (hsupport : ∀ z k,z≠y → F z k=0) (hy : y.natAbs≤ N) :
    (y.natAbs:ℝ)*(F 0 0+
      ∑ k ∈ Finset.range N,(F ((k+1:ℕ):ℤ) (k+1)+F (-((k+1:ℕ):ℤ)) (k+1)))=
      ∑ k ∈ Finset.range N,((k+1:ℕ):ℝ)*
        (F ((k+1:ℕ):ℤ) (k+1)+F (-((k+1:ℕ):ℤ)) (k+1)) := by
  have hf := signed_cell_sum F y N hsupport hy
  have hg := signed_cell_sum (fun z k => (k:ℝ)*F z k) y N (by
    intro z k hz
    rw [hsupport z k hz,mul_zero]) hy
  rw [hf]
  symm
  simpa only [Nat.cast_zero,zero_mul,zero_add,mul_add] using hg

lemma weighted_cellSum (i : Row) (c : ℕ) (g : GuardData)
    {N : ℕ} [Nonempty (Fin N)] (cm : (Fin N → Fin 4) → ℝ)
    (b θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) :
    ((imbalanceSum ω).natAbs:ℝ)*cellSum i c g cm b θ q ω=
      ∑ k ∈ Finset.range N,((k+1:ℕ):ℝ)*rawGuard (xi i) g c cm b ω*
        (safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
          (rawWeight_bounds (xi i) g) c θ ((k+1:ℕ):ℤ) q (k+1) ω+
         safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
          (rawWeight_bounds (xi i) g) c θ (-((k+1:ℕ):ℤ)) q (k+1) ω) := by
  let F : ℤ → ℕ → ℝ := fun y k => if y=0 then
    sampledRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
      (rawWeight_bounds (xi i) g) c θ y q k ω
    else rawGuard (xi i) g c cm b ω*
      safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
        (rawWeight_bounds (xi i) g) c θ y q k ω
  have hh := signed_weighted_cell_sum F (imbalanceSum ω) N (by
    intro y k hy
    dsimp only [F]
    split_ifs
    · exact sampledRow_cell_zero _ _ _ _ _ _ _ _ _ _ hy
    · rw [safeRow_cell_zero _ _ _ _ _ _ _ _ _ _ hy,mul_zero])
    (by rw [← draws_eq_natAbs]; exact draws_le ω)
  have hp (k : ℕ) : ((k+1:ℕ):ℤ)≠0 := by omega
  have hm (k : ℕ) : (-((k+1:ℕ):ℤ))≠0 := by omega
  simpa only [F,if_pos rfl,if_neg (hp _),if_neg (hm _),cellSum,← mul_add,mul_assoc] using hh

theorem normalized_integral_weighted_cellSum (i : Row) (μ : Measure RowRival)
    [IsProbabilityMeasure μ] {N : ℕ} [Nonempty (Fin N)]
    (c : ℕ) (g : GuardData) (cm : (Fin N → Fin 4) → ℝ) {b θ : ℝ}
    (hb : 0< b) (hθ : 0≤θ) (q : ℕ) (hN : 0< N) (hc : (c:ℝ)≤ N)
    (hh : ∀ᵐ r ∂μ,0≤ rawH (xi i) b r) :
    (N:ℝ)*∫ ω : Fin N → RowRival,((imbalanceSum ω).natAbs:ℝ)*cellSum i c g cm b θ q ω
        ∂Measure.pi (fun _ : Fin N => μ)=
      ∑ k ∈ Finset.range N,((k+1:ℕ):ℝ)*
        (safeCell i μ N c g cm b θ ((k+1:ℕ):ℤ) (k+1) q+
         safeCell i μ N c g cm b θ (-((k+1:ℕ):ℤ)) (k+1) q) := by
  let P := Measure.pi (fun _ : Fin N => μ)
  let F := fun y k => fun ω : Fin N → RowRival => rawGuard (xi i) g c cm b ω*
    safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g)
      integerSign (rawWeight_bounds (xi i) g) c θ y q k ω
  have hpositive : ∀ᵐ r ∂μ,0≤ demand (xi i) b r ∧ 0≤ rawH (xi i) b r :=
    hh.mono fun r hr => ⟨(demand_bounds (xi_pos i) hb r).1,hr⟩
  have hF (y : ℤ) (k : ℕ) : Integrable (F y k) P := by
    apply Integrable.of_mem_Icc 0 ((N:ℝ)^q)
      ((measurable_rawGuard (xi i) g c cm b).mul
        (measurable_safeRow (measurable_demand (xi i) b) (measurable_rawH (xi i) b)
          (measurable_rawWeight (xi i) g) measurable_integerSign _ _ _ _ _ _)).aemeasurable
    filter_upwards [polynomial_sampled_ae μ hN _ _ _ _ _ hpositive hc hθ y q k] with ω hω
    have ha := rawGuard_bounds (xi i) g c cm b ω
    exact ⟨mul_nonneg ha.1 hω.2.1,(mul_le_mul_of_nonneg_right ha.2 hω.2.1).trans
      (by simpa only [one_mul] using hω.2.2)⟩
  simp_rw [weighted_cellSum]
  have hid (k : ℕ) (ω : Fin N → RowRival) : ((k+1:ℕ):ℝ)*rawGuard (xi i) g c cm b ω*
      (safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
        (rawWeight_bounds (xi i) g) c θ ((k+1:ℕ):ℤ) q (k+1) ω+
       safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
        (rawWeight_bounds (xi i) g) c θ (-((k+1:ℕ):ℤ)) q (k+1) ω)=
      ((k+1:ℕ):ℝ)*(F ((k+1:ℕ):ℤ) (k+1) ω+F (-((k+1:ℕ):ℤ)) (k+1) ω) := by
    dsimp [F]
    ring
  simp_rw [hid]
  have hJ (k : ℕ) : Integrable (fun ω : Fin N → RowRival =>
      ((k+1:ℕ):ℝ)*(F ((k+1:ℕ):ℤ) (k+1) ω+F (-((k+1:ℕ):ℤ)) (k+1) ω)) P :=
    ((hF _ _).add (hF _ _)).const_mul _
  rw [integral_finsetSum (Finset.range N) (fun k _ => hJ k),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul,integral_add (hF _ _) (hF _ _)]
  dsimp only [safeCell,F,P]
  ring

theorem integral_imbalance_cellSum_le (i : Row) (μ : Measure RowRival)
    [IsProbabilityMeasure μ] {N : ℕ} [Nonempty (Fin N)]
    (c : ℕ) (g : GuardData) (cm : (Fin N → Fin 4) → ℝ) {b θ Q C : ℝ}
    (hb : 0< b) (hθ : 0≤θ) (q : ℕ) (hN : 0< N) (hc : (c:ℝ)≤ N)
    (hh : ∀ᵐ r ∂μ,0≤ rawH (xi i) b r) (hQ0 : 0≤ Q) (hQ1 : Q<1) (hC : 0≤ C)
    (hcell : ∀ k∈Finset.range N,
      safeCell i μ N c g cm b θ ((k+1:ℕ):ℤ) (k+1) q≤ C*Q^(k+1) ∧
      safeCell i μ N c g cm b θ (-((k+1:ℕ):ℤ)) (k+1) q≤ C*Q^(k+1)) :
    (N:ℝ)*∫ ω : Fin N → RowRival,((imbalanceSum ω).natAbs:ℝ)*cellSum i c g cm b θ q ω
        ∂Measure.pi (fun _ : Fin N => μ)≤2*C*Q/(1-Q)^2 := by
  rw [normalized_integral_weighted_cellSum i μ c g cm hb hθ q hN hc hh]
  calc
    _ ≤ ∑ k ∈ Finset.range N,2*C*(((k+1:ℕ):ℝ)*Q^(k+1)) := by
      apply Finset.sum_le_sum
      intro k hk
      have h := mul_le_mul_of_nonneg_left (add_le_add (hcell k hk).1 (hcell k hk).2)
        (Nat.cast_nonneg (k+1) : (0:ℝ)≤(k+1:ℕ))
      convert! h using 1
      ring
    _ = 2*C*(∑ k ∈ Finset.range N,((k+1:ℕ):ℝ)*Q^(k+1)) := by rw [Finset.mul_sum]
    _ ≤ 2*C*(Q/(1-Q)^2) := mul_le_mul_of_nonneg_left
      (finite_weighted_geometric_le hQ0 hQ1 N) (by positivity)
    _ = _ := by ring

end FCAppendix.Affine.Uniform06.ImbalanceWeightedMoment
