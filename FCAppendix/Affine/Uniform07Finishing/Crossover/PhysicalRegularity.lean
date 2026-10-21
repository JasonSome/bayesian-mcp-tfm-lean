import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalKernels
import FCAppendix.Affine.Uniform07Finishing.Crossover.SourceSlope

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology

theorem lipschitz_comp_absolutelyContinuous {f g : ℝ → ℝ} {a b : ℝ}
    {s : Set ℝ} {K : NNReal} (hK : LipschitzOnWith K f s)
    (hg : AbsolutelyContinuousOnInterval g a b) (hmap : MapsTo g (uIcc a b) s) :
    AbsolutelyContinuousOnInterval (fun x => f (g x)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  have hK0 : 0 < (K : ℝ)+1 := by positivity
  obtain ⟨δ,hδ,hbound⟩ := hg (ε/((K : ℝ)+1)) (div_pos hε hK0)
  refine ⟨δ,hδ,?_⟩
  intro E hE hlength
  calc
    _ ≤ ((K : ℝ)+1) * ∑ j ∈ Finset.range E.1, dist (g (E.2 j).1) (g (E.2 j).2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hdist := hK.dist_le_mul _ (hmap (hE.1 j hj).1) _ (hmap (hE.1 j hj).2)
      nlinarith [(dist_nonneg : 0 ≤ dist (g (E.2 j).1) (g (E.2 j).2))]
    _ < ((K : ℝ)+1) * (ε/((K : ℝ)+1)) :=
      mul_lt_mul_of_pos_left (hbound E hE hlength) hK0
    _ = ε := mul_div_cancel₀ ε hK0.ne'

theorem contDiff_comp_absolutelyContinuous
    {f g : ℝ→ℝ} {a b : ℝ}
    (hf : ContDiff ℝ 1 f) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x => f (g x)) a b := by
  obtain ⟨C,hC⟩ := hg.exists_bound
  obtain ⟨K,hK⟩ := (hf.contDiffOn (s := Icc (-C) C)).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  apply lipschitz_comp_absolutelyContinuous hK hg
  intro x hx
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hC x hx)

theorem absolutelyContinuous_inv_of_pos {f : ℝ→ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hpos : ∀ x∈uIcc a b, 0< f x) :
    AbsolutelyContinuousOnInterval (fun x => (f x)⁻¹) a b := by
  obtain ⟨xmin,hxmin,hmin⟩ := isCompact_uIcc.exists_isMinOn
    (show (uIcc a b).Nonempty from ⟨a,left_mem_uIcc⟩) hf.continuousOn
  obtain ⟨B,hB⟩ := hf.exists_bound
  have hlow : 0< f xmin := hpos xmin hxmin
  have hi : ContDiffOn ℝ 1 (fun x : ℝ => x⁻¹) (Icc (f xmin) B) :=
    contDiffOn_id.inv (fun x hx => ne_of_gt (hlow.trans_le hx.1))
  obtain ⟨K,hK⟩ := hi.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  apply lipschitz_comp_absolutelyContinuous hK hf
  intro x hx
  refine ⟨hmin hx,?_⟩
  exact (le_abs_self (f x)).trans (by simpa only [Real.norm_eq_abs] using hB x hx)

theorem absolutelyContinuous_div_of_pos {f g : ℝ→ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hpos : ∀ x∈uIcc a b, 0< g x) :
    AbsolutelyContinuousOnInterval (fun x => f x/g x) a b := by
  simpa only [div_eq_mul_inv] using hf.fun_mul (absolutelyContinuous_inv_of_pos hg hpos)

namespace Physical

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem pureRank_contDiff (m c : ℕ) (t : ℝ) : ContDiff ℝ 1 (pureRank m c t) := by
  unfold pureRank binomBelow PiBinomial.pmf
  fun_prop

theorem comparisonMarginal_ac (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (t : ℝ) {L R : ℝ}
    (hM : AbsolutelyContinuousOnInterval (rank Γ t) L R)
    (hC : AbsolutelyContinuousOnInterval (canonicalMarginal Γ i B) L R) :
    AbsolutelyContinuousOnInterval (comparisonMarginal Γ i B t) L R := by
  exact (contDiff_comp_absolutelyContinuous (pureRank_contDiff m c t) hM).fun_add
    hC

theorem canonical_share_ac (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (t : ℝ) {L R : ℝ}
    (hM : AbsolutelyContinuousOnInterval (rank Γ t) L R)
    (hC : AbsolutelyContinuousOnInterval (canonicalMarginal Γ i B) L R)
    (hq : ∀ b∈uIcc L R, 0< comparisonMarginal Γ i B t b) :
    AbsolutelyContinuousOnInterval
      (fun b => canonicalMarginal Γ i B b/comparisonMarginal Γ i B t b) L R :=
  absolutelyContinuous_div_of_pos hC
    (comparisonMarginal_ac Γ i B t hM hC) hq

theorem residuals_ac (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (t : ℝ) {L R : ℝ}
    (hM : AbsolutelyContinuousOnInterval (rank Γ t) L R)
    (hC : AbsolutelyContinuousOnInterval (canonicalMarginal Γ i B) L R)
    (hR : AbsolutelyContinuousOnInterval (canonicalDuplicate Γ i B) L R)
    (hS : AbsolutelyContinuousOnInterval (success Γ i) L R)
    (hD : AbsolutelyContinuousOnInterval (duplicate Γ i) L R) :
    AbsolutelyContinuousOnInterval (successError Γ i B t) L R ∧
      AbsolutelyContinuousOnInterval (duplicateError Γ i B) L R := by
  have hq := comparisonMarginal_ac Γ i B t hM hC
  exact ⟨hS.fun_sub ((hq.const_mul 2).fun_sub hR),
    hD.fun_sub hR⟩

theorem actual_marginal_ac (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    {L R : ℝ} (hL : 0≤ min L R)
    (hS : AbsolutelyContinuousOnInterval (success Γ i) L R)
    (hD : AbsolutelyContinuousOnInterval (duplicate Γ i) L R) :
    AbsolutelyContinuousOnInterval (q Γ i) L R := by
  have h := (hS.fun_add hD).const_mul (1/2:ℝ)
  apply (absolutelyContinuousOnInterval_iff _ L R).mpr
  intro eps heps
  obtain ⟨delta,hdelta,hbound⟩ :=
    (absolutelyContinuousOnInterval_iff _ L R).mp h eps heps
  refine ⟨delta,hdelta,?_⟩
  intro E hE hlen
  have heq : ∀ b ∈ uIcc L R,
      (1/2:ℝ)*(success Γ i b+duplicate Γ i b)=q Γ i b := by
    intro b hb
    have hbid : 0 ≤ b := hL.trans hb.1
    have hid := success_eq_two_q_sub_duplicate Γ i hbid
    linarith
  have he : (∑ j∈Finset.range E.1,dist (q Γ i (E.2 j).1) (q Γ i (E.2 j).2)) =
      ∑ j∈Finset.range E.1,
        dist ((1/2:ℝ)*(success Γ i (E.2 j).1+duplicate Γ i (E.2 j).1))
          ((1/2:ℝ)*(success Γ i (E.2 j).2+duplicate Γ i (E.2 j).2)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [heq _ (hE.1 j hj).1,heq _ (hE.1 j hj).2]
  rw [he]
  exact hbound E hE hlen

theorem actual_marginal_hasDerivAt (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    {b s' d' : ℝ} (hb : 0< b)
    (hS : HasDerivAt (success Γ i) s' b)
    (hD : HasDerivAt (duplicate Γ i) d' b) :
    HasDerivAt (q Γ i) ((s'+d')/2) b := by
  have h := (hS.add hD).div_const 2
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hb] with z hz
  have hid := success_eq_two_q_sub_duplicate Γ i hz.le
  dsimp
  linarith

def signedResidual (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (eta t b : ℝ) : ℝ :=
  successError Γ i B t b+eta*duplicateError Γ i B b+
    eta*b*deriv (duplicateError Γ i B) b-
    (rank Γ t b-b)*deriv (successError Γ i B t) b

theorem actual_U22_density (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (eta t : ℝ)
    {b M' p' C' R' S' D' : ℝ}
    (hM : HasDerivAt (rank Γ t) M' b)
    (hP : HasDerivAt (pureRank m c t) p' (rank Γ t b))
    (hC : HasDerivAt (canonicalMarginal Γ i B) C' b)
    (hR : HasDerivAt (canonicalDuplicate Γ i B) R' b)
    (hS : HasDerivAt (success Γ i) S' b)
    (hD : HasDerivAt (duplicate Γ i) D' b)
    (hIC : (rank Γ t b-b)*S'=success Γ i b+eta*duplicate Γ i b+eta*b*D') :
    (rank Γ t b-b)*(2*(p'*M'+C')-R')=
      barrierNumerator eta b (comparisonMarginal Γ i B t b)
        (canonicalDuplicate Γ i B b) R'+signedResidual Γ i B eta t b := by
  have hq : HasDerivAt (comparisonMarginal Γ i B t) (p'*M'+C') b :=
    (hP.comp b hM).add hC
  have heS : HasDerivAt (successError Γ i B t) (S'-(2*(p'*M'+C')-R')) b :=
    hS.sub ((hq.const_mul 2).sub hR)
  have heD : HasDerivAt (duplicateError Γ i B) (D'-R') b := hD.sub hR
  unfold signedResidual
  rw [heS.deriv,heD.deriv]
  unfold successError duplicateError barrierNumerator
  nlinarith [hIC]

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
