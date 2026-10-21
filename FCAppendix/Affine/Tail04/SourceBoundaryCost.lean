import FCAppendix.Affine.Tail04.SourceTailCapGap

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceBoundaryCost
open Set Classical
open OriginalValues SourceMenuPopulation SourceMenuIdentity SourceTailTaylor SourceTailCapGap

variable (P : ValueParameters) {ξ lamA lamR t b : ℝ}

lemma failure_lower (hξ : 0< ξ) (hξh : ξ≤1/2)
    (hb : b∈Icc (1:ℝ) (Central.B ξ))
    (hlamA0 : (1-ξ)*Central.B ξ≤ lamA) (hlamA1 : lamA≤1)
    (hlamR0 : (1-ξ)*Central.B ξ≤ lamR) (hlamR1 : lamR≤1) :
    leadingA P ξ lamA lamR*(Central.B ξ-b)^2≤1-served P ξ lamA lamR b := by
  have hB : 1≤ Central.B ξ := by unfold Central.B;linarith
  have hterm (reg : Bool) (lam : ℝ) (hl : (1-ξ)*Central.B ξ≤ lam) (hu : lam≤1) :
      baseFlag P reg*((Central.B ξ-b)/(Central.B ξ-1))^2*
        (1-exposure ξ lam (Central.B ξ))^2≤
      mixedProbability P ξ reg b*(1-exposure ξ lam b)^2 := by
    have hlam : 0≤ lam := (mul_nonneg (by linarith) (by linarith)).trans hl
    have hq := exposure_bounds hξ (by linarith : ξ≤1) hb hl hu
    have hqB := exposure_bounds hξ (by linarith : ξ≤1) ⟨hB,le_rfl⟩ hl hu
    have hm := (exposure_change hξ ⟨hlam,hu⟩ hb).1
    have hs : (1-exposure ξ lam (Central.B ξ))^2≤(1-exposure ξ lam b)^2 := by
      nlinarith [hq.1,hq.2,hqB.1,hqB.2]
    exact mul_le_mul_of_nonneg_left hs
      (mul_nonneg (baseFlag_bounds P reg).1.le (sq_nonneg _))
  have h0 := mul_le_mul_of_nonneg_left (hterm false lamA hlamA0 hlamA1)
    (show 0≤1-P.theta by linarith [P.theta_small])
  have h1 := mul_le_mul_of_nonneg_left (hterm true lamR hlamR0 hlamR1) P.theta_pos.le
  have he : leadingA P ξ lamA lamR*(Central.B ξ-b)^2=
      (1-P.theta)*(baseFlag P false*((Central.B ξ-b)/(Central.B ξ-1))^2*
        (1-exposure ξ lamA (Central.B ξ))^2)+
      P.theta*(baseFlag P true*((Central.B ξ-b)/(Central.B ξ-1))^2*
        (1-exposure ξ lamR (Central.B ξ))^2) := by
    unfold leadingA
    simp only [div_pow]
    ring
  rw [he]
  unfold served
  linarith only [h0,h1]

lemma duplicates_nonneg (hξ : 0< ξ) (hb : b∈Icc (1:ℝ) (Central.B ξ)) :
    0≤ duplicates P ξ lamA lamR b := by
  have h0 := (mixedProbability_bounds P hξ hb false).1
  have h1 := (mixedProbability_bounds P hξ hb true).1
  have hθ := P.theta_pos.le
  have hθ1 : 0≤1-P.theta := by linarith [P.theta_small]
  unfold duplicates
  positivity

theorem cost_lower_quadratic (hξ : 0< ξ) (hξh : ξ≤1/2)
    (ht : Central.B ξ≤ t) (hA : 0≤ leadingA P ξ lamA lamR)
    (hb : b∈Icc (1:ℝ) (Central.B ξ))
    (hlamA0 : (1-ξ)*Central.B ξ≤ lamA) (hlamA1 : lamA≤1)
    (hlamR0 : (1-ξ)*Central.B ξ≤ lamR) (hlamR1 : lamR≤1) :
    endpointCost (leadingA P ξ lamA lamR) (Central.B ξ) (t-Central.B ξ) b≤
      cost P ξ lamA lamR t b := by
  have hF := failure_lower P hξ hξh hb hlamA0 hlamA1 hlamR0 hlamR1
  have hF0 : 0≤1-served P ξ lamA lamR b :=
    (mul_nonneg hA (sq_nonneg _)).trans hF
  have hmul := mul_le_mul_of_nonneg_left hF (sub_nonneg.mpr ht)
  have hreplace := mul_le_mul_of_nonneg_right
    (sub_le_sub_left hb.2 t) hF0
  have hD := duplicates_nonneg P (lamA:=lamA) (lamR:=lamR) hξ hb
  have hp : 0≤(1-2*ξ)*b*duplicates P ξ lamA lamR b := by
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith [hb.1])) hD
  have he : cost P ξ lamA lamR t b=
      b+(t-b)*(1-served P ξ lamA lamR b)+(1-2*ξ)*b*duplicates P ξ lamA lamR b := by
    unfold cost menuUtility payment
    ring
  rw [he]
  unfold endpointCost
  nlinarith only [hmul,hreplace,hp]

theorem cost_lower (hξ : 0< ξ) (hξh : ξ≤1/2)
    (ht : Central.B ξ< t) (hA : 0< leadingA P ξ lamA lamR)
    (hb : b∈Icc (1:ℝ) (Central.B ξ))
    (hlamA0 : (1-ξ)*Central.B ξ≤ lamA) (hlamA1 : lamA≤1)
    (hlamR0 : (1-ξ)*Central.B ξ≤ lamR) (hlamR1 : lamR≤1) :
    Central.B ξ-1/(4*leadingA P ξ lamA lamR*(t-Central.B ξ))≤ cost P ξ lamA lamR t b :=
  ((endpointCost_minimum (leadingA P ξ lamA lamR) (Central.B ξ) (t-Central.B ξ)
    hA (sub_pos.mpr ht)).1 b).trans
    (cost_lower_quadratic P hξ hξh ht.le hA.le hb hlamA0 hlamA1 hlamR0 hlamR1)

lemma comparison_mem {Amin Amax k U : ℝ}
    (_hξ : 0< ξ) (ht : 0< t) (hmin : 0< Amin)
    (ha : Amin≤ leadingA P ξ lamA lamR) (hmax : leadingA P ξ lamA lamR≤ Amax)
    (hk : k<1/(2*Amax)) (hcap : U=Central.B ξ-k/t)
    (hroom : endpointRadius Amin/t≤ Central.B ξ-1) :
    comparison (Central.B ξ) (leadingA P ξ lamA lamR) t∈Icc (1:ℝ) U := by
  have hd := coefficient_distance hmin ha hmax hk
  have hc := div_le_div_of_nonneg_right hd.2.2.2 ht.le
  have he : (1/(2*leadingA P ξ lamA lamR))/t=
      1/(2*leadingA P ξ lamA lamR*t) := by ring
  rw [he] at hc
  constructor
  · unfold comparison
    linarith
  · rw [hcap]
    exact (quadratic_optimizer_lt_cap _ Amax _ k t (hmin.trans_le ha) hmax ht hk).le

theorem comparison_cost_upper {Amin : ℝ}
    (hξ : 0< ξ) (hξh : ξ≤1/2) (ht : 0< t) (hmin : 0< Amin)
    (ha : Amin≤ leadingA P ξ lamA lamR)
    (hb : comparison (Central.B ξ) (leadingA P ξ lamA lamR) t∈Icc (1:ℝ) (Central.B ξ))
    (hlamA0 : (1-ξ)*Central.B ξ≤ lamA) (hlamA1 : lamA≤1)
    (hlamR0 : (1-ξ)*Central.B ξ≤ lamR) (hlamR1 : lamR≤1) :
    cost P ξ lamA lamR t (comparison (Central.B ξ) (leadingA P ξ lamA lamR) t)≤
      Central.B ξ-1/(4*leadingA P ξ lamA lamR*t)+
        taylorConstant ξ (endpointRadius Amin)/t^2 := by
  have hA := hmin.trans_le ha
  have hr : 0≤ endpointRadius Amin := by unfold endpointRadius;positivity
  have hrec : 1/(2*leadingA P ξ lamA lamR)≤ endpointRadius Amin := by
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hnear : Central.B ξ-comparison (Central.B ξ) (leadingA P ξ lamA lamR) t≤
      endpointRadius Amin/t := by
    have hh := div_le_div_of_nonneg_right hrec ht.le
    convert! hh using 1
    unfold comparison
    ring
  have he := scaled_remainder P hξ hξh ht hr hb hnear hlamA0 hlamA1 hlamR0 hlamR1
  have hquad := (endpointCost_minimum (leadingA P ξ lamA lamR) (Central.B ξ) t hA ht).2
  change endpointCost _ _ _ (comparison _ _ _)=_ at hquad
  rw [hquad] at he
  linarith only [(abs_le.mp he).2]

def matchedFloor (t V q : ℝ) : ℝ := t-V/q

theorem exact_match (t V q : ℝ) (hq : q≠0) :
    (t-matchedFloor t V q)*q=V := by
  unfold matchedFloor
  field_simp
  ring

theorem finite_max_cost_bounds {Amin Amax k U eps V : ℝ}
    (hξ : 0< ξ) (hξh : ξ≤1/2) (ht : Central.B ξ< t)
    (hmin : 0< Amin) (hA : Amin≤ leadingA P ξ lamA lamR)
    (hmax : leadingA P ξ lamA lamR≤ Amax) (hk0 : 0< k) (hk : k<1/(2*Amax))
    (hcap : U=Central.B ξ-k/t) (hroom : endpointRadius Amin/t≤ Central.B ξ-1)
    (hlamA0 : (1-ξ)*Central.B ξ≤ lamA) (hlamA1 : lamA≤1)
    (hlamR0 : (1-ξ)*Central.B ξ≤ lamR) (hlamR1 : lamR≤1)
    (g : Icc (1:ℝ) U→ℝ) (a : Icc (1:ℝ) U)
    (hmaximizer : ∀ b,g b≤ g a) (hV : V=g a)
    (herror : ∀ b,|g b-menuUtility P ξ lamA lamR t b|≤ eps) :
    Central.B ξ-1/(4*Amin*(t-Central.B ξ))-eps≤ t-V ∧
      t-V≤ Central.B ξ-1/(4*Amax*t)+
        taylorConstant ξ (endpointRadius Amin)/t^2+eps := by
  have hB0 : 0< Central.B ξ := by unfold Central.B;linarith
  have ht0 := hB0.trans ht
  have hA0 := hmin.trans_le hA
  have hmax0 := hA0.trans_le hmax
  have hUB : U≤ Central.B ξ := by rw [hcap];exact sub_le_self _ (div_nonneg hk0.le ht0.le)
  have hb : ∀ b : Icc (1:ℝ) U,(b:ℝ)∈Icc (1:ℝ) (Central.B ξ) :=
    fun b=>⟨b.2.1,b.2.2.trans hUB⟩
  have hlow := cost_lower P hξ hξh ht hA0 (hb a) hlamA0 hlamA1 hlamR0 hlamR1
  have hE := (abs_le.mp (herror a)).2
  have hrec := one_div_le_one_div_of_le
    (show 0<4*Amin*(t-Central.B ξ) by positivity)
    (mul_le_mul_of_nonneg_right (by linarith : 4*Amin≤4*leadingA P ξ lamA lamR)
      (sub_nonneg.mpr ht.le))
  let a' : Icc (1:ℝ) U := ⟨comparison (Central.B ξ) (leadingA P ξ lamA lamR) t,
    comparison_mem P hξ ht0 hmin hA hmax hk hcap hroom⟩
  have hupper := comparison_cost_upper P hξ hξh ht0 hmin hA (hb a')
    hlamA0 hlamA1 hlamR0 hlamR1
  have hE' := (abs_le.mp (herror a')).1
  have hrec' := one_div_le_one_div_of_le
    (show 0<4*leadingA P ξ lamA lamR*t by positivity)
    (mul_le_mul_of_nonneg_right (by linarith : 4*leadingA P ξ lamA lamR≤4*Amax) ht0.le)
  have hm := hmaximizer a'
  unfold cost at hlow hupper
  rw [hV]
  constructor <;> linarith

theorem floor_localization {B t V q Amin Amax k eps C : ℝ}
    (_hB : 0< B) (_ht : B< t) (_hmin : 0< Amin) (_hmax : 0< Amax)
    (hq : 0< q) (hq1 : q≤1) (hV0 : 0≤ V) (hVt : V≤ t)
    (hcost : B-1/(4*Amin*(t-B))-eps≤ t-V ∧
      t-V≤ B-1/(4*Amax*t)+C/t^2+eps)
    (hlower : 1/(4*Amin*(t-B))+eps+t*(1/q-1)< k/t)
    (hupper : C/t^2+eps<1/(4*Amax*t)) :
    B-k/t< matchedFloor t V q ∧ matchedFloor t V q< B := by
  have hqinv : 0≤1/q-1 := by
    have hh : (1:ℝ)≤1/q := (le_div_iff₀ hq).mpr (by simpa using hq1)
    linarith
  have hm := mul_le_mul_of_nonneg_right hVt hqinv
  have hmn := mul_nonneg hV0 hqinv
  have he : matchedFloor t V q=(t-V)-V*(1/q-1) := by
    unfold matchedFloor
    field_simp [hq.ne']
    ring
  rw [he]
  constructor <;> linarith

end FCAppendix.Affine.Tail04.SourceBoundaryCost
