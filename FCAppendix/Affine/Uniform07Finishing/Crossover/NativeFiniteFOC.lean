import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalWindow
import FCAppendix.Affine.Uniform07Finishing.Crossover.StieltjesAnalytic

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Physical
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
variable {Γ : FiniteGame m 2 c Seed} {t U : ℝ}

theorem native_boundary_broadcast_IC
    (P : BroadcastLaw05 Γ t U)
    (J : Set (Icc (0:ℝ) U)) (hJ : IsOpen J)
    (hsorted : ∀ᵐ z∂(P.lower : Measure (ℝ × Icc (0:ℝ) U)),
      z.2∈J → z.1=rank Γ t z.2.1)
    {b : ℝ} (hb0 : 0< b) (hbU : b≤ U)
    (hbs : b∈(lowerBidMeasure Γ t).support)
    (hbJ : (⟨b,⟨hb0.le,hbU⟩⟩ : Icc (0:ℝ) U)∈J) :
    ∀ i : Fin m, ∀ z∈Icc (0:ℝ) U,
      (problem Γ i).payoff (rank Γ t b) (two z)≤
        (problem Γ i).payoff (rank Γ t b) (two b) := by
  let b' : Icc (0:ℝ) U := ⟨b,⟨hb0.le,hbU⟩⟩
  have h := actual_common_boundary_broadcast_IC_local_at Γ U
    (P.lower : Measure (ℝ × Icc (0:ℝ) U))
    (fun x : Icc (0:ℝ) U => rank Γ t x.1)
    (P.rankContinuous.comp continuous_subtype_val) J hJ hsorted
    P.broadcastIC (P.support_adapter hbs) hbJ
    (fun i => P.payoffContinuous i (rank Γ t b,b') hb0)
  intro i z hz
  simpa only [sourceLowerBroadcastAction_eq_two] using
    h i (⟨z,hz⟩ : Icc (0:ℝ) U)

theorem native_broadcast_FOC_at_support
    (P : BroadcastLaw05 Γ t U)
    {eta : ℝ} (heta0 : 0≤ eta) (heta1 : eta≤ 1)
    (hA : Γ.A=Schedule.affine 2 eta heta0 heta1) (hg : Γ.g=0)
    (J : Set (Icc (0:ℝ) U)) (hJ : IsOpen J)
    (hsorted : ∀ᵐ z∂(P.lower : Measure (ℝ × Icc (0:ℝ) U)),
      z.2∈J → z.1=rank Γ t z.2.1)
    (i : Fin m) {b dS dD : ℝ} (hb0 : 0< b) (hbU : b< U)
    (hbs : b∈(lowerBidMeasure Γ t).support)
    (hbJ : (⟨b,⟨hb0.le,hbU.le⟩⟩ : Icc (0:ℝ) U)∈J)
    (hS : HasDerivAt (success Γ i) dS b)
    (hD : HasDerivAt (duplicate Γ i) dD b) :
    (rank Γ t b-b)*dS=success Γ i b+eta*duplicate Γ i b+eta*b*dD := by
  have hIC := native_boundary_broadcast_IC P J hJ hsorted hb0 hbU.le hbs hbJ
  have hpay (x : ℝ) (hx : 0≤ x) :
      (problem Γ i).payoff (rank Γ t b) (two x)=
        (rank Γ t b-x)*success Γ i x-eta*x*duplicate Γ i x := by
    rw [LowBody.native_affine_zero_fee_payoff Γ heta0 heta1 hA hg]
    simp only [two_bid hx]
    rfl
  have hmax : IsLocalMax
      (fun x => (rank Γ t b-x)*success Γ i x-eta*x*duplicate Γ i x) b := by
    filter_upwards [Ioo_mem_nhds hb0 hbU] with x hx
    have hh := hIC i x ⟨hx.1.le,hx.2.le⟩
    rwa [hpay x hx.1.le,hpay b hb0.le] at hh
  have hlin : HasDerivAt (fun x : ℝ=>rank Γ t b-x) (-1) b := by
    simpa only [Function.comp_def, id_eq] using
      (hasDerivAt_id b).const_sub (rank Γ t b)
  have hη : HasDerivAt (fun x : ℝ=>eta*x) eta b := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hasDerivAt_id b).const_mul eta
  have hd := (hlin.mul hS).sub (hη.mul hD)
  have hz := hmax.hasDerivAt_eq_zero hd
  nlinarith

theorem common_density_from_native_finite_IC
    (P : BroadcastLaw05 Γ t U)
    {eta L R : ℝ} (heta0 : 0≤ eta) (heta1 : eta≤ 1)
    (hA : Γ.A=Schedule.affine 2 eta heta0 heta1) (hg : Γ.g=0)
    (hLR : L≤ R) (hL : 0< L) (hRU : R≤ U)
    (J : Set (Icc (0:ℝ) U)) (hJ : IsOpen J)
    (hcontains : ∀ b (hb : b∈Icc L R),
      (⟨b,⟨hL.le.trans hb.1,hb.2.trans hRU⟩⟩ : Icc (0:ℝ) U)∈J)
    (hsorted : ∀ᵐ z∂(P.lower : Measure (ℝ × Icc (0:ℝ) U)),
      z.2∈J → z.1=rank Γ t z.2.1)
    (i : Fin m)
    (hM : AbsolutelyContinuousOnInterval (rank Γ t) L R)
    (hS : AbsolutelyContinuousOnInterval (success Γ i) L R)
    (hD : AbsolutelyContinuousOnInterval (duplicate Γ i) L R) :
    ∀ᵐ b∂(volume : Measure ℝ), b∈Icc L R →
      HasDerivAt (rank Γ t) (deriv (rank Γ t) b) b ∧
      HasDerivAt (success Γ i) (deriv (success Γ i) b) b ∧
      HasDerivAt (duplicate Γ i) (deriv (duplicate Γ i) b) b ∧
      (b∈(lowerBidMeasure Γ t).support →
        (rank Γ t b-b)*deriv (success Γ i) b=
          success Γ i b+eta*duplicate Γ i b+eta*b*deriv (duplicate Γ i) b) := by
  have hne : ∀ᵐ b∂(volume : Measure ℝ), b≠U := by
    rw [ae_iff]
    simp
  filter_upwards [StieltjesAnalytic.common_derivatives_of_three_AC hM hS hD,hne]
    with b hb hne hbI
  have hd := hb (by simpa only [uIcc_of_le hLR] using hbI)
  refine ⟨hd.1,hd.2.1,hd.2.2,?_⟩
  intro hbs
  have hb0 : 0< b := hL.trans_le hbI.1
  have hbU : b< U := lt_of_le_of_ne (hbI.2.trans hRU) hne
  exact native_broadcast_FOC_at_support P heta0 heta1 hA hg J hJ hsorted i
    hb0 hbU hbs (hcontains b hbI) hd.2.1 hd.2.2

end FCAppendix.Affine.Uniform07Finishing.Crossover.Physical
