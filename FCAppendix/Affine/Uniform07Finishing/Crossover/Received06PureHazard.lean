import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Regularity
import FCAppendix.Affine.LowBody.BinomialBoundary

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open Set Filter Topology Uniform06
open scoped BigOperators

private theorem bernoulli_nonnegative (x : ℝ) (hx : 0≤ x) (n : ℕ) :
    1+(n:ℝ)*x≤(1+x)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh:=mul_le_mul_of_nonneg_right ih (by linarith : 0≤ 1+x)
    have hsq:=mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)
    rw [pow_succ]
    push_cast
    nlinarith only [hh,hsq]

private theorem geometric_sum_identity (r : ℝ) (n : ℕ) :
    (∑j∈Finset.range n,r^j)*(1-r)=1-r^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,pow_succ]; nlinarith only [ih]

theorem crossover_geometric_sum_lower :
    (498:ℝ)≤∑j∈Finset.range 4000,(499/500:ℝ)^j := by
  have hb:=bernoulli_nonnegative (1/499) (by norm_num) 500
  have hb' : (2:ℝ)≤(500/499:ℝ)^500 := by
    rw [show (1:ℝ)+1/499=500/499 by norm_num] at hb
    exact (show (2:ℝ)≤ 1+(500:ℕ)*(1/499) by norm_num).trans hb
  have hid : (499/500:ℝ)^500*(500/499:ℝ)^500=1 := by
    rw [←mul_pow]
    norm_num
  have hp : 0≤(499/500:ℝ)^500 := by positivity
  have hmul:=mul_le_mul_of_nonneg_left hb' hp
  rw [hid] at hmul
  have h500 : (499/500:ℝ)^500≤ 1/2 :=
    (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr hmul
  have h4000:=pow_le_pow_left₀ hp h500 8
  rw [←pow_mul] at h4000
  change (499/500:ℝ)^4000≤(1/2:ℝ)^8 at h4000
  have hs:=geometric_sum_identity (499/500) 4000
  rw [show (1:ℝ)-499/500=1/500 by norm_num] at hs
  rw [show (1/2:ℝ)^8=1/256 by norm_num] at h4000
  generalize hpow : (499/500:ℝ)^4000=a at hs h4000
  nlinarith only [hs,h4000]

private theorem finite_sum_reflection (n : ℕ) (f : ℕ→ℝ) :
    (∑j∈Finset.range n,f j)=∑j∈Finset.range n,f (n-1-j) := by
  apply Finset.sum_bij (fun j _=>n-1-j)
  · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
  · intro j hj k hk he; simp only [Finset.mem_range] at hj hk; omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    exact ⟨n-1-j,by simp only [Finset.mem_range]; omega,by omega⟩
  · intro j hj; simp only [Finset.mem_range] at hj; congr 1; omega

theorem binomial_backward_geometric (N k : ℕ) {p r : ℝ}
    (hp : p∈Ioc (0:ℝ) (1/2)) (_hr : 0≤ r) (hk : k< N)
    (hkr : r*(N-k:ℕ)≤(k+1:ℕ)) :
    r*PiBinomial.pmf N p (k+1)≤ PiBinomial.pmf N p k := by
  have hden : 0<(N-k:ℕ)*p := mul_pos (Nat.cast_pos.mpr (by omega)) hp.1
  have he:=LowBody.pmf_adjacent N k p hk
  have hstep:=mul_le_mul_of_nonneg_right hkr hp.1.le
  have hhalf:=mul_le_mul_of_nonneg_left
    (show p≤ 1-p by linarith [hp.2]) (Nat.cast_nonneg (k+1))
  have hmass:=BinomialPivotal.pmf_nonneg N (k+1) ⟨hp.1.le,by linarith [hp.2]⟩
  have hmul:=mul_le_mul_of_nonneg_right (hstep.trans hhalf) hmass
  rw [he] at hmul
  apply (mul_le_mul_iff_right₀ hden).mp
  nlinarith only [hmul]

theorem source_backward_ratio {m : ℕ} (hm : 10000000000≤ m)
    {j : ℕ} (hj : j<4000) :
    (499/500:ℝ)*((m-1)-(Uniform07.capacity m-1-j-1):ℕ)≤
      ((Uniform07.capacity m-1-j-1)+1:ℕ) := by
  have hcap:=(Uniform06.PhysicalRates.capacity_floor_bounds m).1
  have hcup:=(Uniform06.PhysicalRates.capacity_floor_bounds m).2
  have hmR : (10000000000:ℝ)≤ m:=by exact_mod_cast hm
  have hjR : (j:ℝ)≤ 3999:=by exact_mod_cast (show j≤ 3999 by omega)
  have hc4001 : 4001≤ Uniform07.capacity m := by
    by_contra hh
    have hsmall : (Uniform07.capacity m:ℝ)≤ 4000:=by exact_mod_cast (show Uniform07.capacity m≤ 4000 by omega)
    norm_num only [Uniform07.rho] at hcap
    linarith
  have hcN : Uniform07.capacity m≤ m-1 :=
    (Uniform06.PhysicalRates.capacity_strictly_below_rivals (by omega)).le
  have hk : Uniform07.capacity m-1-j-1≤ m-1 := by omega
  have hkcast : ((Uniform07.capacity m-1-j-1:ℕ):ℝ)=
      (Uniform07.capacity m:ℝ)-1-j-1 := by
    rw [Nat.cast_sub (by omega : 1≤ Uniform07.capacity m-1-j),
      Nat.cast_sub (by omega : j≤ Uniform07.capacity m-1),
      Nat.cast_sub (by omega : 1≤ Uniform07.capacity m)]
    norm_num
  have hright : ((Uniform07.capacity m-1-j-1+1:ℕ):ℝ)=
      (Uniform07.capacity m:ℝ)-1-j := by
    rw [Nat.cast_add_one,hkcast]
    ring
  rw [Nat.cast_sub hk,Nat.cast_sub (by omega : 1≤ m),hkcast,hright]
  norm_num only [Nat.cast_one,Uniform07.rho] at hcap hcup ⊢
  linarith

theorem source_tail_dominates_boundary {m : ℕ} (hm : 10000000000≤ m)
    {p : ℝ} (hp : p∈Ioc (0:ℝ) (1/2)) :
    498*PiBinomial.pmf (m-1) p (Uniform07.capacity m-1)≤
      Bayes.binomBelow (m-1) p (Uniform07.capacity m) := by
  have hcap:=(Uniform06.PhysicalRates.capacity_floor_bounds m).1
  have hmR : (10000000000:ℝ)≤ m:=by exact_mod_cast hm
  have hc4001 : 4001≤ Uniform07.capacity m := by
    by_contra hh
    have hsmall : (Uniform07.capacity m:ℝ)≤ 4000:=by exact_mod_cast (show Uniform07.capacity m≤ 4000 by omega)
    norm_num only [Uniform07.rho] at hcap
    linarith
  have hcN:=Uniform06.PhysicalRates.capacity_strictly_below_rivals (show 4≤ m by omega)
  have hmass:=BinomialPivotal.pmf_nonneg (m-1) (Uniform07.capacity m-1)
    ⟨hp.1.le,by linarith [hp.2]⟩
  have hchain : ∀j,j<4000→(499/500:ℝ)^j*
      PiBinomial.pmf (m-1) p (Uniform07.capacity m-1)≤
        PiBinomial.pmf (m-1) p (Uniform07.capacity m-1-j) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hh:=mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num : (0:ℝ)≤ 499/500)
      have hs:=binomial_backward_geometric (m-1) (Uniform07.capacity m-1-j-1)
        hp (by norm_num : (0:ℝ)≤ 499/500) (by omega) (source_backward_ratio hm (by omega : j<4000))
      have he : Uniform07.capacity m-1-j-1+1=Uniform07.capacity m-1-j := by omega
      rw [he] at hs
      have he' : Uniform07.capacity m-1-(j+1)=Uniform07.capacity m-1-j-1 := by omega
      rw [he']
      calc
        (499/500:ℝ)^(j+1)*PiBinomial.pmf (m-1) p (Uniform07.capacity m-1)=
            (499/500:ℝ)*((499/500:ℝ)^j*PiBinomial.pmf (m-1) p (Uniform07.capacity m-1)) := by
          rw [pow_succ]
          ring
        _≤_:=hh.trans hs
  calc
    498*PiBinomial.pmf (m-1) p (Uniform07.capacity m-1)≤
        (∑j∈Finset.range 4000,(499/500:ℝ)^j)*
          PiBinomial.pmf (m-1) p (Uniform07.capacity m-1):=
      mul_le_mul_of_nonneg_right crossover_geometric_sum_lower hmass
    _≤∑j∈Finset.range 4000,PiBinomial.pmf (m-1) p (Uniform07.capacity m-1-j):=by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun j hj=>hchain j (Finset.mem_range.mp hj))
    _≤∑j∈Finset.range (Uniform07.capacity m),PiBinomial.pmf (m-1) p (Uniform07.capacity m-1-j):=by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro j _ _
      exact BinomialPivotal.pmf_nonneg _ _ ⟨hp.1.le,by linarith [hp.2]⟩
    _=Bayes.binomBelow (m-1) p (Uniform07.capacity m):=by
      exact (finite_sum_reflection (Uniform07.capacity m) (fun j=>PiBinomial.pmf (m-1) p j)).symm

theorem binomial_deleted_mass_identity (N k : ℕ) (hk : k< N) (p : ℝ) :
    (N:ℝ)*PiBinomial.pmf (N-1) p k*(1-p)=
      (N-k:ℕ)*PiBinomial.pmf N p k := by
  have hN : N-1+1=N:=by omega
  have hc:=Nat.choose_mul_succ_eq (N-1) k
  rw [hN] at hc
  have hcR : ((N-1).choose k:ℝ)*(N:ℝ)=(N.choose k:ℝ)*(N-k:ℕ):=by exact_mod_cast hc
  have he : N-k=(N-1-k)+1:=by omega
  unfold PiBinomial.pmf
  rw [show (1-p)^(N-k)=(1-p)^(N-1-k)*(1-p) by rw [he,pow_succ]]
  linear_combination (p^k*(1-p)^(N-1-k)*(1-p))*hcR

theorem source_pivotal_upper {m : ℕ} (hm : 10000000000≤ m)
    {p : ℝ} (hp : p∈Ioc (0:ℝ) (1/2)) :
    (m-1:ℕ)*PiBinomial.pmf (m-2) p (Uniform07.capacity m-1)≤
      (21/10000:ℝ)*(m:ℝ)*Bayes.binomBelow (m-1) p (Uniform07.capacity m) := by
  have hcpos:=Uniform06.PhysicalRates.capacity_positive (show 3≤ m by omega)
  have hcN:=Uniform06.PhysicalRates.capacity_strictly_below_rivals (show 4≤ m by omega)
  have hc:=(Uniform06.PhysicalRates.capacity_floor_bounds m).1
  have hmR : (10000000000:ℝ)≤ m:=by exact_mod_cast hm
  have hnum : ((m-1)-(Uniform07.capacity m-1):ℕ)≤(51/100:ℝ)*(m:ℝ) := by
    rw [show m-1-(Uniform07.capacity m-1)=m-Uniform07.capacity m by omega,
      Nat.cast_sub (by omega : Uniform07.capacity m≤ m)]
    norm_num only [Uniform07.rho] at hc
    linarith
  have hmass:=BinomialPivotal.pmf_nonneg (m-1) (Uniform07.capacity m-1)
    ⟨hp.1.le,by linarith [hp.2]⟩
  have hD : 0≤(m-1:ℕ)*PiBinomial.pmf (m-2) p (Uniform07.capacity m-1):=
    mul_nonneg (Nat.cast_nonneg _) (BinomialPivotal.pmf_nonneg _ _ ⟨hp.1.le,by linarith [hp.2]⟩)
  have hid:=binomial_deleted_mass_identity (m-1) (Uniform07.capacity m-1) (by omega) p
  rw [show m-1-1=m-2 by omega] at hid
  have hd:=mul_le_mul_of_nonneg_left (show (1/2:ℝ)≤ 1-p by linarith [hp.2]) hD
  have hn:=mul_le_mul_of_nonneg_right hnum hmass
  rw [hid] at hd
  have hbound : (m-1:ℕ)*PiBinomial.pmf (m-2) p (Uniform07.capacity m-1)≤
      (51/50:ℝ)*(m:ℝ)*PiBinomial.pmf (m-1) p (Uniform07.capacity m-1) := by
    nlinarith only [hd,hn]
  have htail:=mul_le_mul_of_nonneg_left (source_tail_dominates_boundary hm hp)
    (show (0:ℝ)≤(21/10000:ℝ)*(m:ℝ) by positivity)
  have hnonneg:=mul_nonneg (Nat.cast_nonneg m) hmass
  nlinarith only [hbound,htail,hnonneg]

theorem source_rank_polynomial_derivative (row : Uniform07.Row) {m : ℕ} (hm : 4≤ m) (w : ℝ) :
    HasDerivAt (Physical.pureRank m (Uniform07.capacity m) (Uniform07.cutoff row))
      (SharpPureDerivative.rankSlope row m w) w := by
  have hc:=Uniform06.PhysicalRates.capacity_positive (show 3≤ m by omega)
  have hcn:=Uniform06.PhysicalRates.capacity_strictly_below_rivals hm
  have hh:=(BinomialPivotal.hasDerivAt_binomBelow (m-2) (Uniform07.capacity m-1)
    (by omega) ((1+Uniform07.cutoff row)/2-w)).comp w
      ((hasDerivAt_id w).const_sub ((1+Uniform07.cutoff row)/2))
  rw [show m-2+1=m-1 by omega,show Uniform07.capacity m-1+1=Uniform07.capacity m by omega] at hh
  have hcntR : ((m-2:ℕ):ℝ)+1=((m-1:ℕ):ℝ) := by
    exact_mod_cast (show m-2+1=m-1 by omega)
  convert! hh using 1
  simp only [SharpPureDerivative.rankSlope]
  rw [←hcntR]
  ring

theorem source_rank_polynomial_upper (row : Uniform07.Row) {m : ℕ} (hm : 10000000000≤ m)
    {w : ℝ} (hw : w∈Icc (Uniform07.cutoff row/2) (Uniform07.cutoff row)) :
    0< deriv (Physical.pureRank m (Uniform07.capacity m) (Uniform07.cutoff row)) w ∧
    deriv (Physical.pureRank m (Uniform07.capacity m) (Uniform07.cutoff row)) w≤
      (21/10000:ℝ)*(m:ℝ)*Physical.pureRank m (Uniform07.capacity m) (Uniform07.cutoff row) w := by
  rw [(source_rank_polynomial_derivative row (by omega : 4≤ m) w).deriv]
  have hp : (1+Uniform07.cutoff row)/2-w∈Ioc (0:ℝ) (1/2) := by
    have ht1:=Uniform07.cutoff_lt_one row
    constructor <;> linarith [hw.1,hw.2]
  have hcN:=Uniform06.PhysicalRates.capacity_strictly_below_rivals (show 4≤ m by omega)
  refine ⟨mul_pos (Nat.cast_pos.mpr (by omega))
    (BinomialPivotal.pmf_pos _ _ (by omega) ⟨hp.1,by linarith [hp.2]⟩),?_⟩
  exact source_pivotal_upper hm hp

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
