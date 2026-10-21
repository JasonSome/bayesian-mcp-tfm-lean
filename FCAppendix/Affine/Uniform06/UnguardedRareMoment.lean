import FCAppendix.Affine.Uniform06.RawMomentPartition

noncomputable section
namespace FCAppendix.Affine.Uniform06.UnguardedRareMoment

open Set MeasureTheory Filter LowBody
open scoped Topology BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open FiniteSampledLaplace SampledCellDomination SampledSafeLimit RawMomentPartition
open MixedIntervalLLT

variable {N : ℕ} [Nonempty (Fin N)]

def unguardedRow (i : Row) (c : ℕ) (g : GuardData) (b θ : ℝ) (q : ℕ)
    (ω : Fin N → RowRival) : ℝ :=
  if imbalanceSum ω=0 then 0 else
    safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
      (rawWeight_bounds (xi i) g) c θ (imbalanceSum ω) q (imbalanceSum ω).natAbs ω

def unguardedCell (i : Row) (μ : Measure RowRival) (N c : ℕ) [Nonempty (Fin N)]
    (g : GuardData) (b θ : ℝ) (q k : ℕ) (y : ℤ) : ℝ :=
  (N:ℝ)*∫ ω : Fin N → RowRival,
    safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
      (rawWeight_bounds (xi i) g) c θ y q k ω ∂Measure.pi (fun _ : Fin N => μ)

lemma unguardedRow_eq_sum (i : Row) (c : ℕ) (g : GuardData) (b θ : ℝ)
    (q : ℕ) (ω : Fin N → RowRival) :
    unguardedRow i c g b θ q ω=
      ∑ k ∈ Finset.range N,
        (safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
          (rawWeight_bounds (xi i) g) c θ ((k+1:ℕ):ℤ) q (k+1) ω+
         safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
          (rawWeight_bounds (xi i) g) c θ (-((k+1:ℕ):ℤ)) q (k+1) ω) := by
  let F : ℤ → ℕ → ℝ := fun y k => if y=0 then 0 else
    safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
      (rawWeight_bounds (xi i) g) c θ y q k ω
  have h := signed_cell_sum F (imbalanceSum ω) N (by
    intro y k hy
    dsimp only [F]
    split_ifs
    · rfl
    · exact safeRow_cell_zero _ _ _ _ _ _ _ _ _ _ hy)
    (by rw [← draws_eq_natAbs]; exact draws_le ω)
  have hp (k : ℕ) : ((k+1:ℕ):ℤ)≠0 := by omega
  have hm (k : ℕ) : (-((k+1:ℕ):ℤ))≠0 := by omega
  simpa only [F,if_pos rfl,if_neg (hp _),if_neg (hm _),zero_add,unguardedRow] using h.symm

lemma measurable_unguardedRow (i : Row) (c : ℕ) (g : GuardData) (b θ : ℝ) (q : ℕ) :
    Measurable (unguardedRow (N:=N) i c g b θ q) := by
  change Measurable (fun ω : Fin N → RowRival => unguardedRow i c g b θ q ω)
  simp_rw [unguardedRow_eq_sum]
  apply Finset.measurable_sum
  intro k hk
  exact (measurable_safeRow (measurable_demand (xi i) b) (measurable_rawH (xi i) b)
    (measurable_rawWeight (xi i) g) measurable_integerSign _ _ _ _ _ _).add
    (measurable_safeRow (measurable_demand (xi i) b) (measurable_rawH (xi i) b)
      (measurable_rawWeight (xi i) g) measurable_integerSign _ _ _ _ _ _)

lemma unguardedRow_nonneg (i : Row) (c : ℕ) (g : GuardData) (b θ : ℝ)
    (q : ℕ) (ω : Fin N → RowRival) : 0≤ unguardedRow i c g b θ q ω := by
  unfold unguardedRow
  split_ifs
  · rfl
  · exact safeRow_nonneg _ _ _ _ _ _ _ _ _ _ _

lemma unguardedRow_polynomial (i : Row) (μ : Measure RowRival) [IsProbabilityMeasure μ]
    (c : ℕ) (g : GuardData) {b θ : ℝ} (hb : 0< b) (hθ : 0≤θ)
    (q : ℕ) (hN : 0< N) (hc : (c:ℝ)≤ N) (hh : ∀ᵐ r ∂μ,0≤ rawH (xi i) b r) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => μ),unguardedRow i c g b θ q ω∈Icc (0:ℝ) ((N:ℝ)^q) := by
  have he (j : Fin N) := (measurePreserving_eval (fun _ : Fin N => μ) j).quasiMeasurePreserving.ae hh
  filter_upwards [ae_all_iff.mpr he] with ω hω
  unfold unguardedRow
  split_ifs
  · exact ⟨le_rfl,by positivity⟩
  · have hp := (row_polynomial_bounds (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g)
      integerSign (rawWeight_bounds (xi i) g) c θ (imbalanceSum ω) q (imbalanceSum ω).natAbs ω
      hN (fun j => (demand_bounds (xi_pos i) hb (ω j)).1) hω hc hθ).1
    exact ⟨safeRow_nonneg _ _ _ _ _ _ _ _ _ _ _,
      (safe_le_sampled _ _ _ _ _ _ _ _ _ _ _).trans hp.2⟩

lemma integral_unguardedRow (i : Row) (μ : Measure RowRival) [IsProbabilityMeasure μ]
    (c : ℕ) (g : GuardData) {b θ : ℝ} (hb : 0< b) (hθ : 0≤θ)
    (q : ℕ) (hN : 0< N) (hc : (c:ℝ)≤ N) (hh : ∀ᵐ r ∂μ,0≤ rawH (xi i) b r) :
    (N:ℝ)*∫ ω : Fin N → RowRival,unguardedRow i c g b θ q ω ∂Measure.pi (fun _ : Fin N => μ)=
      ∑ k ∈ Finset.range N,(unguardedCell i μ N c g b θ q (k+1) ((k+1:ℕ):ℤ)+
        unguardedCell i μ N c g b θ q (k+1) (-((k+1:ℕ):ℤ))) := by
  have hpositive : ∀ᵐ r ∂μ,0≤ demand (xi i) b r ∧ 0≤ rawH (xi i) b r :=
    hh.mono fun r hr => ⟨(demand_bounds (xi_pos i) hb r).1,hr⟩
  have hi (y : ℤ) (k : ℕ) : Integrable
      (safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
        (rawWeight_bounds (xi i) g) c θ y q k : (Fin N → RowRival) → ℝ)
        (Measure.pi (fun _ : Fin N => μ)) :=
    Integrable.of_mem_Icc 0 ((N:ℝ)^q)
      (measurable_safeRow (measurable_demand (xi i) b) (measurable_rawH (xi i) b)
        (measurable_rawWeight (xi i) g) measurable_integerSign _ _ _ _ _ _).aemeasurable
      ((polynomial_sampled_ae μ hN _ _ _ _ _ hpositive hc hθ y q k).mono fun _ hx => hx.2)
  simp_rw [unguardedRow_eq_sum]
  have hsum (k : ℕ) : Integrable (fun ω : Fin N → RowRival =>
      safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
        (rawWeight_bounds (xi i) g) c θ ((k+1:ℕ):ℤ) q (k+1) ω+
      safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
        (rawWeight_bounds (xi i) g) c θ (-((k+1:ℕ):ℤ)) q (k+1) ω)
      (Measure.pi (fun _ : Fin N => μ)) := (hi _ _).add (hi _ _)
  rw [integral_finsetSum (Finset.range N) (fun k _ => hsum k),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_add (hi _ _) (hi _ _),mul_add]
  rfl

lemma finite_geometric_tail_le {Q : ℝ} (hQ0 : 0≤ Q) (hQ1 : Q<1) (N : ℕ) :
    (∑ k ∈ Finset.range N,Q^(k+1))≤ Q/(1-Q) := by
  have he : (1-Q)*(∑ k ∈ Finset.range N,Q^(k+1))=Q-Q^(N+1) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ,mul_add,ih,pow_succ]; ring
  apply (le_div_iff₀ (sub_pos.mpr hQ1)).mpr
  rw [mul_comm,he]
  linarith [pow_nonneg hQ0 (N+1)]

theorem integral_unguardedRow_le (i : Row) (μ : Measure RowRival) [IsProbabilityMeasure μ]
    (c : ℕ) (g : GuardData) {b θ C Q : ℝ} (hb : 0< b) (hθ : 0≤θ)
    (q : ℕ) (hN : 0< N) (hc : (c:ℝ)≤ N) (hh : ∀ᵐ r ∂μ,0≤ rawH (xi i) b r)
    (hC : 0≤ C) (hQ0 : 0≤ Q) (hQ1 : Q<1)
    (hcell : ∀ k∈Finset.range N,
      unguardedCell i μ N c g b θ q (k+1) ((k+1:ℕ):ℤ)≤ C*Q^(k+1) ∧
      unguardedCell i μ N c g b θ q (k+1) (-((k+1:ℕ):ℤ))≤ C*Q^(k+1)) :
    (N:ℝ)*∫ ω : Fin N → RowRival,unguardedRow i c g b θ q ω ∂Measure.pi (fun _ : Fin N => μ)≤
      2*C*Q/(1-Q) := by
  rw [integral_unguardedRow i μ c g hb hθ q hN hc hh]
  calc
    _ ≤ ∑ k ∈ Finset.range N,2*C*Q^(k+1) := by
      apply Finset.sum_le_sum
      intro k hk
      nlinarith [(hcell k hk).1,(hcell k hk).2]
    _ = 2*C*(∑ k ∈ Finset.range N,Q^(k+1)) := by rw [Finset.mul_sum]
    _ ≤ 2*C*(Q/(1-Q)) := mul_le_mul_of_nonneg_left
      (finite_geometric_tail_le hQ0 hQ1 N) (by positivity)
    _ = _ := by ring

theorem eventual_unguarded_bound (i : Row) (A : CenteredArray RowRival)
    [∀ n,Nonempty (Fin (A.N n))] (hgap : A.CompactGap)
    (b θ r : ℕ → ℝ) (c : ℕ → ℕ) (g : ℕ → GuardData)
    (hb : ∀ n,0< b n) (hY : ∀ n,A.Y n=integerSign)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=demand (xi i) (b n) x-r n)
    (hcap : ∀ n,(c n:ℝ)≤ A.N n)
    {lo hi η : ℝ} (hlo : 0< lo) (hθ : ∀ n,lo≤θ n ∧ θ n≤ hi) (hη : 0<η)
    (hh : ∀ n,∀ᵐ x ∂A.law n,0≤ rawH (xi i) (b n) x ∧
      (0< rawWeight (xi i) (g n) x → η≤ rawH (xi i) (b n) x)) :
    ∃ B>0,∀ᶠ n in atTop,∀ q : Fin 3,
      (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
        unguardedRow i (c n) (g n) (b n) (θ n) q.val ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)≤ B := by
  let Q := Real.exp (-lo*η)
  have hQ0 : 0< Q := Real.exp_pos _
  have hQ1 : Q<1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hlo hη])
  obtain ⟨C,hC,hcells⟩ := eventual_sampled_cell_bounds A hgap
    (fun n => demand (xi i) (b n)) (fun n => rawH (xi i) (b n))
    (fun n => rawWeight (xi i) (g n)) r (fun n => (c n:ℝ)) θ
    (fun n => measurable_demand _ _) (fun n => measurable_rawH _ _)
    (fun n => measurable_rawWeight _ _) (fun n => rawWeight_bounds _ _)
    (fun n => demand_bounds (xi_pos i) (hb n)) (fun n => (hh n).mono fun _ h => h.1)
    hcenter hcap hlo hθ hη (fun n => (hh n).mono fun _ h => h.2)
  refine ⟨2*C*Q/(1-Q),by positivity,?_⟩
  filter_upwards [hcells] with n hn q
  apply integral_unguardedRow_le i (A.law n) (c n) (g n) (hb n)
    (hlo.le.trans (hθ n).1) q.val (Nat.cast_pos.mp (A.N_pos n)) (hcap n)
    ((hh n).mono fun _ h => h.1) hC.le hQ0.le hQ1
  intro k hk
  simp only [hY] at hn
  simpa only [unguardedCell,Q] using! ⟨hn ((k+1:ℕ):ℤ) (k+1) q,
    hn (-((k+1:ℕ):ℤ)) (k+1) q⟩

end FCAppendix.Affine.Uniform06.UnguardedRareMoment
