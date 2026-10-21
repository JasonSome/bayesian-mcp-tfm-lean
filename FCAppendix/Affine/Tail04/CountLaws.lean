import FCAppendix.Finite.ConditionalCountLaw
import FCAppendix.Probability.IndependentCounts
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace FCAppendix.Affine.Tail04.Counts
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open scoped BigOperators

def countPair (z : Bool × Bool) : Fin 3 :=
  ⟨(if z.1 then 1 else 0)+(if z.2 then 1 else 0), by
    rcases z with ⟨x,y⟩
    cases x <;> cases y <;> norm_num⟩

def pairLaw (p q : ℝ) (hp : p∈Icc 0 1) (hq : q∈Icc 0 1) : CountLaw 2 :=
  ((IndependentCounts.bernoulli p hp.1 hp.2).prod
    (IndependentCounts.bernoulli q hq.1 hq.2)).map countPair

theorem pairLaw_expect (p q : ℝ) (hp : p∈Icc 0 1) (hq : q∈Icc 0 1)
    (f : Fin 3 → ℝ) :
    (pairLaw p q hp hq).expect f =
      (1-p)*(1-q)*f 0+(p*(1-q)+(1-p)*q)*f 1+p*q*f 2 := by
  unfold pairLaw
  rw [FiniteLaw.expect_map,FiniteLaw.expect_prod,IndependentCounts.expect_bernoulli]
  simp only [IndependentCounts.expect_bernoulli]
  change (1-p)*((1-q)*f 0+q*f 1)+p*((1-q)*f 1+q*f 2)=_
  ring

theorem pairLaw_statistics (p q : ℝ) (hp : p∈Icc 0 1) (hq : q∈Icc 0 1) :
    (pairLaw p q hp hq).success=1-(1-p)*(1-q) ∧
      (pairLaw p q hp hq).duplicates=p*q ∧
      (pairLaw p q hp hq).load=p+q := by
  have hs : (pairLaw p q hp hq).success=1-(1-p)*(1-q) := by
    rw [CountLaw.success,pairLaw_expect]
    norm_num [successIndicator]
    ring
  have hl : (pairLaw p q hp hq).load=p+q := by
    rw [CountLaw.load,pairLaw_expect]
    norm_num
    ring
  exact ⟨hs,by rw [CountLaw.duplicates,hl,hs]; ring,hl⟩

def activeLaw (e p q : ℝ) (he : e∈Icc 0 1)
    (hp : p∈Icc 0 1) (hq : q∈Icc 0 1) : CountLaw 2 :=
  FiniteLaw.mixture (pairLaw p q hp hq) (FiniteLaw.dirac 1) e he.1 he.2

theorem activeLaw_expect (e p q : ℝ) (he : e∈Icc 0 1)
    (hp : p∈Icc 0 1) (hq : q∈Icc 0 1) (f : Fin 3 → ℝ) :
    (activeLaw e p q he hp hq).expect f =
      e*((1-p)*(1-q)*f 0+(p*(1-q)+(1-p)*q)*f 1+p*q*f 2)+(1-e)*f 1 := by
  rw [activeLaw,FiniteLaw.expect_mixture,pairLaw_expect,FiniteLaw.expect_dirac]

theorem activeLaw_statistics (e p q : ℝ) (he : e∈Icc 0 1)
    (hp : p∈Icc 0 1) (hq : q∈Icc 0 1) :
    (activeLaw e p q he hp hq).success=1-e*(1-p)*(1-q) ∧
      (activeLaw e p q he hp hq).duplicates=e*p*q ∧
      (activeLaw e p q he hp hq).load=1+e*(p+q-1) := by
  have hs : (activeLaw e p q he hp hq).success=1-e*(1-p)*(1-q) := by
    rw [CountLaw.success,activeLaw_expect]
    norm_num [successIndicator]
    ring
  have hl : (activeLaw e p q he hp hq).load=1+e*(p+q-1) := by
    rw [CountLaw.load,activeLaw_expect]
    norm_num
    ring
  exact ⟨hs,by rw [CountLaw.duplicates,hl,hs]; ring,hl⟩

def regimeLaw (θ : ℝ) (hθ : θ∈Icc 0 1) (KA KR : CountLaw 2) : CountLaw 2 :=
  FiniteLaw.mixture KA KR (1-θ) (sub_nonneg.mpr hθ.2) (by linarith [hθ.1])

theorem regimeLaw_expect (θ : ℝ) (hθ : θ∈Icc 0 1)
    (KA KR : CountLaw 2) (f : Fin 3 → ℝ) :
    (regimeLaw θ hθ KA KR).expect f=(1-θ)*KA.expect f+θ*KR.expect f := by
  rw [regimeLaw,FiniteLaw.expect_mixture]
  ring

def twoRegimeLaw (θ eA eR qA qR : ℝ) (hθ : θ∈Icc 0 1)
    (heA : eA∈Icc 0 1) (heR : eR∈Icc 0 1)
    (hqA : qA∈Icc 0 1) (hqR : qR∈Icc 0 1) : CountLaw 2 :=
  regimeLaw θ hθ (activeLaw eA qA qA heA hqA hqA)
    (activeLaw eR qR qR heR hqR hqR)

theorem twoRegimeLaw_statistics (θ eA eR qA qR : ℝ) (hθ : θ∈Icc 0 1)
    (heA : eA∈Icc 0 1) (heR : eR∈Icc 0 1)
    (hqA : qA∈Icc 0 1) (hqR : qR∈Icc 0 1) :
    let K := twoRegimeLaw θ eA eR qA qR hθ heA heR hqA hqR
    K.success=1-((1-θ)*eA*(1-qA)^2+θ*eR*(1-qR)^2) ∧
      K.duplicates=(1-θ)*eA*qA^2+θ*eR*qR^2 ∧
      K.load=1+(1-θ)*eA*(2*qA-1)+θ*eR*(2*qR-1) := by
  dsimp only
  have hA := activeLaw_statistics eA qA qA heA hqA hqA
  have hR := activeLaw_statistics eR qR qR heR hqR hqR
  have hs : (twoRegimeLaw θ eA eR qA qR hθ heA heR hqA hqR).success=
      1-((1-θ)*eA*(1-qA)^2+θ*eR*(1-qR)^2) := by
    change (regimeLaw θ hθ _ _).expect _ = _
    rw [regimeLaw_expect]
    change (1-θ)*(activeLaw eA qA qA heA hqA hqA).success+
      θ*(activeLaw eR qR qR heR hqR hqR).success = _
    rw [hA.1,hR.1]
    ring
  have hl : (twoRegimeLaw θ eA eR qA qR hθ heA heR hqA hqR).load=
      1+(1-θ)*eA*(2*qA-1)+θ*eR*(2*qR-1) := by
    change (regimeLaw θ hθ _ _).expect _ = _
    rw [regimeLaw_expect]
    change (1-θ)*(activeLaw eA qA qA heA hqA hqA).load+
      θ*(activeLaw eR qR qR heR hqR hqR).load = _
    rw [hA.2.2,hR.2.2]
    ring
  exact ⟨hs,by rw [CountLaw.duplicates,hl,hs]; ring,hl⟩

def singletonLaw (p : ℝ) (hp : p∈Icc 0 1) : CountLaw 2 :=
  FiniteLaw.mixture (FiniteLaw.dirac 1) (FiniteLaw.dirac 0) p hp.1 hp.2

theorem singletonLaw_statistics (p : ℝ) (hp : p∈Icc 0 1) :
    (singletonLaw p hp).success=p ∧ (singletonLaw p hp).duplicates=0 ∧
      (singletonLaw p hp).load=p := by
  have hs : (singletonLaw p hp).success=p := by
    simp [singletonLaw,CountLaw.success,FiniteLaw.expect_mixture,successIndicator]
  have hl : (singletonLaw p hp).load=p := by
    simp [singletonLaw,CountLaw.load,FiniteLaw.expect_mixture]
  exact ⟨hs,by rw [CountLaw.duplicates,hl,hs,sub_self],hl⟩

theorem count_masses (K : CountLaw 2) :
    K.mass 0=1-K.success ∧ K.mass 1=K.success-K.duplicates ∧
      K.mass 2=K.duplicates := by
  have ht := K.total
  norm_num [Fin.sum_univ_succ] at ht
  have hs : K.success=K.mass 1+K.mass 2 := by
    norm_num [CountLaw.success,FiniteLaw.expect,Fin.sum_univ_succ,successIndicator]
  have hl : K.load=K.mass 1+2*K.mass 2 := by
    norm_num [CountLaw.load,FiniteLaw.expect,Fin.sum_univ_succ]
    ring
  have hd : K.duplicates=K.mass 2 := by rw [CountLaw.duplicates,hl,hs]; ring
  exact ⟨by linarith,by linarith,hd.symm⟩

theorem eq_of_success_duplicates (K J : CountLaw 2)
    (hS : K.success=J.success) (hD : K.duplicates=J.duplicates) : K=J := by
  have hK := count_masses K
  have hJ := count_masses J
  apply FiniteLaw.ext
  intro r
  fin_cases r
  · change K.mass (0:Fin 3)=J.mass 0
    rw [hK.1,hJ.1,hS]
  · change K.mass (1:Fin 3)=J.mass 1
    rw [hK.2.1,hJ.2.1,hS,hD]
  · change K.mass (2:Fin 3)=J.mass 2
    rw [hK.2.2,hJ.2.2,hD]

theorem mass_tendsto_of_success_duplicates (K : ℕ→ CountLaw 2) (J : CountLaw 2)
    (hS : Tendsto (fun k => (K k).success) atTop (𝓝 J.success))
    (hD : Tendsto (fun k => (K k).duplicates) atTop (𝓝 J.duplicates)) :
    ∀ r, Tendsto (fun k => (K k).mass r) atTop (𝓝 (J.mass r)) := by
  intro r
  fin_cases r
  · change Tendsto (fun k => (K k).mass (0:Fin 3)) atTop (𝓝 (J.mass 0))
    simp_rw [(count_masses (K _)).1,(count_masses J).1]
    exact tendsto_const_nhds.sub hS
  · change Tendsto (fun k => (K k).mass (1:Fin 3)) atTop (𝓝 (J.mass 1))
    simp_rw [(count_masses (K _)).2.1,(count_masses J).2.1]
    exact hS.sub hD
  · change Tendsto (fun k => (K k).mass (2:Fin 3)) atTop (𝓝 (J.mass 2))
    simp_rw [(count_masses (K _)).2.2,(count_masses J).2.2]
    exact hD

section NativeAggregation
variable (N c : ℕ→ℕ) (Seed : ℕ→ Type*) [∀ k,MeasurableSpace (Seed k)]
variable (Γ : ∀ k,FiniteGame (N k) 2 (c k) (Seed k)) (hN : ∀ k,0< N k)
variable (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k,(Γ k).F=F)

include hF in
theorem native_expect_integral_tendsto (J : ℝ→ CountLaw 2)
    (hlim : ∀ r,∀ᵐ v∂F,
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hN k) v).mass r)
        atTop (𝓝 ((J v).mass r))) (f : Fin 3→ℝ) :
    Tendsto (fun k => ∫ v,
      (conditionalTypeCountLaw (Γ k) (hN k) v).expect f ∂(Γ k).F)
      atTop (𝓝 (∫ v,(J v).expect f ∂F)) := by
  simp_rw [hF]
  apply tendsto_integral_of_dominated_convergence
    (fun _ => ∑ r : Fin 3,‖f r‖)
    (fun k => (measurable_conditionalTypeCountLaw_expect (Γ k) (hN k) f).aestronglyMeasurable)
    (integrable_const _)
  · intro k
    exact Filter.Eventually.of_forall (fun v =>
      (conditionalTypeCountLaw (Γ k) (hN k) v).norm_expect_le_sum_norm f)
  · have hall : ∀ᵐ v∂F,∀ r,
        Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hN k) v).mass r)
          atTop (𝓝 ((J v).mass r)) := ae_all_iff.mpr hlim
    filter_upwards [hall] with v hv
    exact tendsto_finsetSum Finset.univ (fun r _ => (hv r).mul_const (f r))

include F hF in
theorem native_coverage_tendsto (J : ℝ→ CountLaw 2)
    (hlim : ∀ r,∀ᵐ v∂F,
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hN k) v).mass r)
        atTop (𝓝 ((J v).mass r))) :
    Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 (∫ v,(J v).success ∂F)) := by
  have h := native_expect_integral_tendsto N c Seed Γ hN F hF J hlim
    (fun r => successIndicator r.val)
  change Tendsto (fun k => ∫ v,(conditionalTypeCountLaw (Γ k) (hN k) v).success ∂(Γ k).F)
    atTop (𝓝 (∫ v,(J v).success ∂F)) at h
  simpa only [integral_conditionalTypeCountLaw_success] using h

include F hF in
theorem native_load_tendsto (J : ℝ→ CountLaw 2)
    (hlim : ∀ r,∀ᵐ v∂F,
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hN k) v).mass r)
        atTop (𝓝 ((J v).mass r))) :
    Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 (∫ v,(J v).load ∂F)) := by
  have h := native_expect_integral_tendsto N c Seed Γ hN F hF J hlim
    (fun r => (r.val:ℝ))
  change Tendsto (fun k => ∫ v,(conditionalTypeCountLaw (Γ k) (hN k) v).load ∂(Γ k).F)
    atTop (𝓝 (∫ v,(J v).load ∂F)) at h
  simpa only [integral_conditionalTypeCountLaw_load] using h

include F hF in
theorem native_duplicates_tendsto (J : ℝ→ CountLaw 2)
    (hlim : ∀ r,∀ᵐ v∂F,
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hN k) v).mass r)
        atTop (𝓝 ((J v).mass r))) :
    Tendsto (fun k => finiteLoad (Γ k)-finiteCoverage (Γ k))
      atTop (𝓝 (∫ v,(J v).duplicates ∂F)) := by
  have h := native_expect_integral_tendsto N c Seed Γ hN F hF J hlim
    (fun r => (r.val:ℝ)-successIndicator r.val)
  simpa only [←CountLaw.duplicates_eq_expect,integral_conditionalTypeCountLaw_duplicates] using h

end NativeAggregation
end FCAppendix.Affine.Tail04.Counts
