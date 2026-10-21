import FCAppendix.Affine.Tail04.OriginalActiveCrossingCarrier

noncomputable section
namespace FCAppendix.Affine.Tail04.ActiveNoisyClusterGeometry
open MeasureTheory ProbabilityTheory Set Classical
open OriginalActiveCrossingCarrier

variable {X : Type*} [MeasurableSpace X]

def physical (eps : ℝ) (base : X → ℝ) (noise : X → unitInterval) (x : X) : ℝ :=
  base x*(1+eps*(noise x:ℝ))

def raised (eps b r : ℝ) (noise : X → unitInterval) (x : X) : ℝ :=
  (b+2*r)*(1+eps*(noise x:ℝ))

def openCluster (active : Set X) (base : X → ℝ) (b r : ℝ) : Set X :=
  active∩base ⁻¹' Ioo (b-r) (b+r)

def closedCluster (active : Set X) (base : X → ℝ) (b r : ℝ) : Set X :=
  active∩base ⁻¹' Icc (b-3*r) (b+3*r)

lemma measurable_physical (eps : ℝ) (base : X → ℝ) (hb : Measurable base)
    (noise : X → unitInterval) (hn : Measurable noise) :
    Measurable (physical eps base noise) :=
  hb.mul (measurable_const.add (measurable_const.mul (measurable_subtype_coe.comp hn)))

lemma measurable_raised (eps b r : ℝ) (noise : X → unitInterval) (hn : Measurable noise) :
    Measurable (raised eps b r noise) :=
  measurable_const.mul (measurable_const.add
    (measurable_const.mul (measurable_subtype_coe.comp hn)))

lemma measurableSet_openCluster (active : Set X) (ha : MeasurableSet active)
    (base : X → ℝ) (hb : Measurable base) (b r : ℝ) :
    MeasurableSet (openCluster active base b r) := ha.inter (hb measurableSet_Ioo)

lemma measurableSet_closedCluster (active : Set X) (ha : MeasurableSet active)
    (base : X → ℝ) (hb : Measurable base) (b r : ℝ) :
    MeasurableSet (closedCluster active base b r) := ha.inter (hb measurableSet_Icc)

lemma factor_bounds {eps : ℝ} (heps : 0≤ eps) (u : unitInterval) :
    1≤1+eps*(u:ℝ) ∧ 1+eps*(u:ℝ)≤1+eps := by
  constructor <;> nlinarith [u.2.1,u.2.2]

omit [MeasurableSpace X] in
lemma physical_bounds {eps C : ℝ} (heps : 0≤ eps)
    (base : X → ℝ) (noise : X → unitInterval) (x : X)
    (hb : base x∈Icc (1:ℝ) C) :
    base x≤ physical eps base noise x ∧
      physical eps base noise x≤ base x+eps*C := by
  have hz := factor_bounds heps (noise x)
  have h0 : 0≤ base x := (by norm_num : (0:ℝ)≤1).trans hb.1
  have hnoise : eps*(noise x:ℝ)≤eps := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (noise x).2.2 heps
  have hmul : base x*(eps*(noise x:ℝ))≤ eps*C := by
    calc
      _ ≤ base x*eps := mul_le_mul_of_nonneg_left hnoise h0
      _ ≤ C*eps := mul_le_mul_of_nonneg_right hb.2 heps
      _ = _ := mul_comm _ _
  dsimp [physical]
  constructor
  · nlinarith [mul_nonneg h0 (mul_nonneg heps (noise x).2.1)]
  · nlinarith only [hmul]

omit [MeasurableSpace X] in

theorem open_cluster_geometry {eps C b r : ℝ} (heps : 0≤ eps) (heps1 : eps≤1)
    (hr : 0< r) (hnoise : eps*C≤ r) (hdev : b+2*r≤ C)
    (active : Set X) (base : X → ℝ) (noise : X → unitInterval)
    (hsupport : ∀ x∈active,base x∈Icc (1:ℝ) C)
    (x : X) (hx : x∈openCluster active base b r) :
    b-r< physical eps base noise x ∧
      physical eps base noise x< raised eps b r noise x ∧
      b+2*r≤ raised eps b r noise x ∧ raised eps b r noise x≤ b+3*r ∧
      raised eps b r noise x-physical eps base noise x<6*r := by
  have hbase := hsupport x hx.1
  have hc : b-r< base x ∧ base x< b+r := hx.2
  have hz := factor_bounds heps (noise x)
  have hp := physical_bounds heps base noise x hbase
  have hd0 : 0< b+2*r := by linarith [hbase.1,hc.2]
  have hgap : 0<(b+2*r)-base x := by linarith
  have hdelta : raised eps b r noise x-physical eps base noise x=
      ((b+2*r)-base x)*(1+eps*(noise x:ℝ)) := by dsimp [raised,physical];ring
  have hsmall : ((b+2*r)-base x)*(1+eps*(noise x:ℝ))<6*r := by
    have h0 : 0≤1+eps*(noise x:ℝ) := by linarith [hz.1]
    have h1 : 1+eps*(noise x:ℝ)≤2 := by linarith [hz.2]
    have hh := mul_le_mul_of_nonneg_left h1 hgap.le
    nlinarith
  have hraise : raised eps b r noise x≤ b+2*r+eps*C := by
    have hn : (b+2*r)*(eps*(noise x:ℝ))≤ eps*C := by
      calc
        _ ≤ (b+2*r)*eps := mul_le_mul_of_nonneg_left
          (show eps*(noise x:ℝ)≤eps from by simpa only [mul_one] using mul_le_mul_of_nonneg_left (noise x).2.2 heps) hd0.le
        _ ≤ C*eps := mul_le_mul_of_nonneg_right hdev heps
        _ = _ := mul_comm _ _
    dsimp [raised]
    nlinarith only [hn]
  refine ⟨hc.1.trans_le hp.1,?_,?_,by linarith,?_⟩
  · have hh : 0< raised eps b r noise x-physical eps base noise x := by
      rw [hdelta]
      exact mul_pos hgap (by linarith [hz.1])
    linarith
  · dsimp [raised]
    nlinarith [mul_nonneg hd0.le (mul_nonneg heps (noise x).2.1)]
  · rw [hdelta]
    exact hsmall

omit [MeasurableSpace X] in
theorem cluster_rival_below_raised {eps C b r : ℝ}
    (heps : 0≤ eps) (hr : 0< r) (hnoise : eps*C≤ r)
    (active : Set X) (base : X → ℝ) (noise : X → unitInterval)
    (hsupport : ∀ x∈active,base x∈Icc (1:ℝ) C)
    (x y : X) (hx : x∈openCluster active base b r) (hy : y∈openCluster active base b r) :
    physical eps base noise y< raised eps b r noise x := by
  have hp := physical_bounds heps base noise y (hsupport y hy.1)
  have hcy : base y< b+r := hy.2.2
  have hcx : base x< b+r := hx.2.2
  have hbx : 1≤ base x := (hsupport x hx.1).1
  have hd0 : 0≤ b+2*r := by linarith
  have hz0 : 0≤ eps*(noise x:ℝ) := mul_nonneg heps (noise x).2.1
  dsimp [raised]
  nlinarith [mul_nonneg hd0 hz0]

omit [MeasurableSpace X] in

theorem crossing_mem_closedCluster {eps C b r : ℝ}
    (heps : 0≤ eps) (heps1 : eps≤1) (hr : 0< r)
    (hnoise : eps*C≤ r) (hdev : b+2*r≤ C)
    (active : Set X) (base : X → ℝ) (noise : X → unitInterval)
    (hsupport : ∀ x∈active,base x∈Icc (1:ℝ) C)
    (x y : X) (hx : x∈openCluster active base b r)
    (hcross : crossing active (physical eps base noise) (raised eps b r noise) x y) :
    y∈closedCluster active base b r := by
  have hg := open_cluster_geometry heps heps1 hr hnoise hdev active base noise hsupport x hx
  have hp := physical_bounds heps base noise y (hsupport y hcross.1)
  refine ⟨hcross.1,?_,?_⟩ <;> linarith [hcross.2.1,hcross.2.2]

omit [MeasurableSpace X] in
theorem orderedCoordinate_le_crossing {N : ℕ} {eps C b r : ℝ}
    (heps : 0≤ eps) (hr : 0< r) (hnoise : eps*C≤ r)
    (active : Set X) (base : X → ℝ) (noise : X → unitInterval)
    (hsupport : ∀ x∈active,base x∈Icc (1:ℝ) C)
    (x : X) (hx : x∈openCluster active base b r) (row : Fin (N+1) → X) (j : Fin (N+1)) :
    orderedCoordinate (openCluster active base b r) (physical eps base noise) j (x,row)≤
      if crossing active (physical eps base noise) (raised eps b r noise) x (row j) then 1 else 0 := by
  by_cases h : row j∈openCluster active base b r ∧
      physical eps base noise x≤ physical eps base noise (row j)
  · have hc : crossing active (physical eps base noise) (raised eps b r noise) x (row j) :=
      ⟨h.1.1,h.2,(cluster_rival_below_raised heps hr hnoise active base noise hsupport x (row j) hx h.1).le⟩
    simp only [orderedCoordinate,if_pos h,if_pos hc,le_refl]
  · simp only [orderedCoordinate,if_neg h]
    split_ifs <;> norm_num

end FCAppendix.Affine.Tail04.ActiveNoisyClusterGeometry
