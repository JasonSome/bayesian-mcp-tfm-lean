import FCAppendix.Affine.Hybrid.Native02.OriginalPopulation
import FCAppendix.Affine.Hybrid.PopulationUpper
import FCAppendix.Finite.CapacityFill

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes

theorem component_visible_zero
    (P : ProbabilityMeasure (ℝ×JointAction 2)) (t : ℝ) (j : Fin 2)
    (hP : ∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),x.2.bid ≤ t) :
    ((P : Measure (ℝ×JointAction 2)).prod (permLaw 2))
      {u : UserDraw 2 | j∈ firstK u.2 u.1.2.routeCount ∧ t<u.1.2.bid}=0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  have hp := (measurePreserving_fst (μ:=(P : Measure (ℝ×JointAction 2)))
    (ν:=permLaw 2)).quasiMeasurePreserving.ae hP
  filter_upwards [hp] with u hu hmem
  exact (not_lt.mpr hu) hmem.2

theorem component_visible_fixed_route
    (P : ProbabilityMeasure (ℝ×JointAction 2)) (t : ℝ) (j : Fin 2)
    (k : ℕ) (hk : k ≤ 2)
    (hP : ∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),t<x.2.bid ∧ x.2.routeCount=k) :
    ((P : Measure (ℝ×JointAction 2)).prod (permLaw 2))
      {u : UserDraw 2 | j∈ firstK u.2 u.1.2.routeCount ∧ t<u.1.2.bid}=
      ENNReal.ofReal ((k:ℝ)/2) := by
  have hp := (measurePreserving_fst (μ:=(P : Measure (ℝ×JointAction 2)))
    (ν:=permLaw 2)).quasiMeasurePreserving.ae hP
  have he : (fun u : UserDraw 2 => j∈ firstK u.2 u.1.2.routeCount ∧ t<u.1.2.bid)
      =ᵐ[((P : Measure (ℝ×JointAction 2)).prod (permLaw 2))]
      (fun u : UserDraw 2 => u ∈
        univ×ˢ{tau : Equiv.Perm (Fin 2) | j∈ firstK tau k}) := by
    filter_upwards [hp] with u hu
    apply propext
    simp only [mem_prod,mem_univ,mem_setOf_eq,true_and,hu.1,hu.2,and_true]
  have hmeasure : ((P : Measure (ℝ×JointAction 2)).prod (permLaw 2))
      {u : UserDraw 2 | j∈ firstK u.2 u.1.2.routeCount ∧ t<u.1.2.bid} =
      ((P : Measure (ℝ×JointAction 2)).prod (permLaw 2))
        (univ×ˢ{tau : Equiv.Perm (Fin 2) | j∈ firstK tau k}) := measure_congr he
  rw [hmeasure,Measure.prod_prod,measure_univ,one_mul]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact permLaw_mem_firstK 2 k (by norm_num) hk j

theorem original_population_active_visible_mass {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m 2 c Seed)
    (s a h d : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hjoint : G.F⊗ₘG.σ=populationJoint s a h PL PA PH)
    (hL : ∀ᵐx ∂(PL : Measure (ℝ×JointAction 2)),x.2.bid ≤ d)
    (hA : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),d<x.2.bid ∧ x.2.routeCount=2)
    (hH : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),d<x.2.bid ∧ x.2.routeCount=1)
    (j : Fin 2) : alphaGt G j d=a+h/2 := by
  have hprob : userLaw G {u : UserDraw 2 |
      j∈ firstK u.2 u.1.2.routeCount ∧ d<u.1.2.bid}=
      ENNReal.ofReal (a+h/2) := by
    rw [userLaw,hjoint,populationJoint,Measure.add_prod,Measure.add_prod,
      Measure.prod_smul_left,Measure.prod_smul_left,Measure.prod_smul_left]
    simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,
      component_visible_zero PL d j hL,
      component_visible_fixed_route PA d j 2 (by norm_num) hA,
      component_visible_fixed_route PH d j 1 (by norm_num) hH]
    norm_num only [Nat.cast_ofNat,div_self (by norm_num : (2:ℝ)≠0),Nat.cast_one,
      ENNReal.ofReal_one,mul_zero,mul_one,zero_add]
    rw [←ENNReal.ofReal_mul hh,←ENNReal.ofReal_add ha (by positivity)]
    congr 1
    ring
  change (userLaw G {u : UserDraw 2 |
    j∈ firstK u.2 u.1.2.routeCount ∧ d<u.1.2.bid}).toReal=_
  rw [hprob,ENNReal.toReal_ofReal (by positivity)]

theorem visible_atomless_of_original_components {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m 2 c Seed) (s a h : ℝ)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hjoint : G.F⊗ₘG.σ=populationJoint s a h PL PA PH)
    (hL : ∀ b : ℝ,(PL : Measure (ℝ×JointAction 2)) {x | x.2.bid=b}=0)
    (hA : ∀ b : ℝ,(PA : Measure (ℝ×JointAction 2)) {x | x.2.bid=b}=0)
    (hH : ∀ b : ℝ,(PH : Measure (ℝ×JointAction 2)) {x | x.2.bid=b}=0) :
    VisibleAtomless G := by
  intro j b
  have hz : (G.F⊗ₘG.σ) {x | x.2.bid=b}=0 := by
    simp only [hjoint,populationJoint,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
      hL b,hA b,hH b,mul_zero,add_zero]
  have hproj : userLaw G {u : UserDraw 2 | u.1.2.bid=b}=0 := by
    change ((G.F⊗ₘG.σ).prod (permLaw 2)) {u : UserDraw 2 | u.1.2.bid=b}=0
    rw [show {u : UserDraw 2 | u.1.2.bid=b} = {x | x.2.bid=b}×ˢuniv by ext u; simp]
    rw [Measure.prod_prod,hz,zero_mul]
  exact measure_mono_null (fun _ hu=>hu.2) hproj

theorem two_proposer_schedule_floor (A : Schedule 2) (r : ℕ)
    (hr : 0<r) (hr2 : r ≤ 2) : (1/2:ℝ)*r ≤ A.charge r := by
  have hrR : (r:ℝ) ≤ 2 := by exact_mod_cast hr2
  exact (show (1/2:ℝ)*r ≤ 1 by linarith).trans (A.lower r hr hr2)

theorem original_population_load_tendsto {M C : ℕ→ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : ∀ k,FiniteGame (M k) 2 (C k) Seed)
    (s a h d rho : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) (hd : 0<d)
    (hgap : rho<a+h/2)
    (PL PA PH : ℕ→ ProbabilityMeasure (ℝ×JointAction 2))
    (hjoint : ∀ k,(G k).F⊗ₘ(G k).σ=populationJoint s a h (PL k) (PA k) (PH k))
    (hL : ∀ k,∀ᵐx ∂(PL k : Measure (ℝ×JointAction 2)),x.2.bid ≤ d)
    (hA : ∀ k,∀ᵐx ∂(PA k : Measure (ℝ×JointAction 2)),d<x.2.bid ∧ x.2.routeCount=2)
    (hH : ∀ k,∀ᵐx ∂(PH k : Measure (ℝ×JointAction 2)),d<x.2.bid ∧ x.2.routeCount=1)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k=>(C k:ℝ)/(M k:ℝ)) atTop (𝓝 rho))
    (hproposers : ∀ k j,ProposerRationalOnPath (G k) j) :
    Tendsto (fun k=>finiteLoad (G k)) atTop (𝓝 (2*rho)) := by
  apply tendsto_finiteLoad_of_visible_tail M C G (0:Fin 2) (fun _=>1/2) d rho hd hM
    (Eventually.of_forall (fun _=>by norm_num)) hcap hproposers
    (fun k r hr hr2=>two_proposer_schedule_floor (G k).A r hr hr2)
  intro eps heps
  apply Eventually.of_forall
  intro k
  rw [original_population_active_visible_mass (G k) s a h d ha hh
    (PL k) (PA k) (PH k) (hjoint k) (hL k) (hA k) (hH k) 0]
  linarith

end FCAppendix.Affine.Hybrid.Native02
