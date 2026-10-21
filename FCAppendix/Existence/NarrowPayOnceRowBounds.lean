import FCAppendix.Existence.NarrowPayOnceUniformScore
import FCAppendix.Existence.NarrowPayOnceExpectedScore

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators

variable {R n c : ℕ}

theorem profileScore_increment_error (hn : 2≤n) (hc : c≤R+1)
    {lower upper B w w0 eta : ℝ} (hlower : 0<lower)
    (hp : ∀b∈bidBox (ι:=Fin (R+1)) lower upper,∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1)
    (hd : ∀b∈bidBox (ι:=Fin (R+1)) lower upper,
      ‖fderiv ℝ (profileScore n c w) b-fderiv ℝ (profileScore n c w0) (fun _=>B)‖≤eta)
    (a b : Fin (R+1)→ℝ) (ha : a∈bidBox lower upper) (hb : b∈bidBox lower upper) :
    |profileScore n c w b-profileScore n c w a-
      fderiv ℝ (profileScore n c w0) (fun _=>B) (b-a)|≤eta*‖b-a‖ := by
  let L := fderiv ℝ (profileScore n c w0) (fun _ : Fin (R+1)=>B)
  have hf (d : Fin (R+1)→ℝ) (hd' : d∈bidBox lower upper) :
      DifferentiableAt ℝ (profileScore n c w) d :=
    differentiableAt_profileScore hn hc w d (fun i=>hlower.trans_le (hd' i).1) (hp d hd')
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ)
    (f:=fun d=>profileScore n c w d-L d)
    (fun d hd'=> (hf d hd').sub L.differentiableAt)
    (fun d hd'=>by
      change ‖fderiv ℝ (profileScore n c w - (fun x=>L x)) d‖≤eta
      rw [fderiv_sub (hf d hd') L.differentiableAt,L.fderiv]
      exact hd d hd')
    (bidBox_convex lower upper) ha hb
  rw [Real.norm_eq_abs] at hh
  change |profileScore n c w b-profileScore n c w a-L (b-a)|≤_
  have heq : profileScore n c w b-profileScore n c w a-L (b-a)=
      (profileScore n c w b-L b)-(profileScore n c w a-L a) := by
    rw [map_sub]
    ring
  rw [heq]
  exact hh

theorem finiteRowScore_eq_profileScore (hn : 2≤n) (hc : c≤R+1)
    {V : Type*} (beta : V→ℝ) (w z : ℝ) (omega : Fin R→V)
    (hz : 0<z) (hbeta : ∀v,0<beta v)
    (hp : ∀i,kernelMarginal n c (rowBids beta z omega) i∈Ioo (0:ℝ) 1) :
    finiteRowScore n c beta w z omega=profileScore n c w (rowBids beta z omega) := by
  have hd := hasDerivAt_finiteRowMarginal hn hc beta z omega hz hbeta hp
  have hK := (contDiffAt_kernelMarginal_interior hn (by simpa using hc)
    (rowBids beta z omega) (by
      intro i; refine Fin.cases hz (fun j=>hbeta (omega j)) i) hp).differentiableAt (by simp)
  have he : HasDerivAt (fun x=>rowBids beta x omega) (focalDirection R) z := by
    apply hasDerivAt_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact hasDerivAt_id z
    · exact hasDerivAt_const z (beta (omega j))
  have hh := hasDerivAt_pi.mp (hK.hasFDerivAt.comp_hasDerivAt z he) 0
  have hv : finiteRowVelocity n c beta z omega=
      fderiv ℝ (kernelMarginal n c) (rowBids beta z omega) (focalDirection R) 0 := hd.unique hh
  simp only [finiteRowScore,profileScore,finiteRowMarginal,hv,rowBids,Fin.cons_zero]

theorem profileScore_type_bound (hn : 2≤n) (hc : c≤R+1)
    {lower upper : ℝ} (hlower : 0<lower) (b : Fin (R+1)→ℝ)
    (hb : b∈bidBox lower upper) (hp : ∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1)
    (w v : ℝ) :
    |profileScore n c w b-profileScore n c v b|≤
      (n:ℝ)*firstJetBound n lower*|w-v| := by
  have hK := norm_fderiv_kernelMarginal_le hn (by simpa using hc) hlower b
    (fun i=>(hb i).1) hp
  have hu : |fderiv ℝ (kernelMarginal n c) b (focalDirection R) 0|≤firstJetBound n lower := by
    have hi := norm_le_pi_norm (fderiv ℝ (kernelMarginal n c) b (focalDirection R)) 0
    have h := hi.trans (((fderiv ℝ (kernelMarginal n c) b).le_opNorm (focalDirection R)).trans
      (mul_le_mul_of_nonneg_right hK (norm_nonneg _)))
    simpa only [Real.norm_eq_abs,norm_focalDirection,mul_one,firstJetBound] using h
  have hz : 0≤1-kernelMarginal n c b 0 := by linarith [(hp 0).2]
  have hz1 : 1-kernelMarginal n c b 0≤1 := by linarith [(hp 0).1]
  have he : profileScore n c w b-profileScore n c v b=(w-v)*(n:ℝ)*
      (1-kernelMarginal n c b 0)^(n-1)*fderiv ℝ (kernelMarginal n c) b (focalDirection R) 0 := by
    dsimp [profileScore]
    ring
  have hnabs : |(n:ℝ)|=(n:ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
  simp only [he,abs_mul,hnabs,abs_of_nonneg (pow_nonneg hz (n-1))]
  have hA : 0≤firstJetBound n lower := by unfold firstJetBound; positivity
  calc
    _≤(|w-v| * (n:ℝ))*1*firstJetBound n lower := by
      gcongr
      exact pow_le_one₀ hz hz1
    _=_ := by ring

theorem norm_rowBids_sub_le {V : Type*} (beta gamma : V→ℝ)
    (x y D : ℝ) (omega : Fin R→V) (hD : 0≤D) (hxy : |y-x|≤D)
    (hbg : ∀v,|gamma v-beta v|≤D) :
    ‖rowBids gamma y omega-rowBids beta x omega‖≤D := by
  apply (pi_norm_le_iff_of_nonneg hD).mpr
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · simpa only [Real.norm_eq_abs,Pi.sub_apply,rowBids,Fin.cons_zero] using hxy
  · simpa only [Real.norm_eq_abs,Pi.sub_apply,rowBids,Fin.cons_succ] using hbg (omega j)

theorem norm_rowBids_sub_same {V : Type*} (beta : V→ℝ)
    (x y : ℝ) (omega : Fin R→V) :
    ‖rowBids beta y omega-rowBids beta x omega‖=|y-x| := by
  apply le_antisymm
  · exact norm_rowBids_sub_le beta beta x y |y-x| omega (abs_nonneg _) le_rfl
      (fun _=>by simp)
  · simpa only [Real.norm_eq_abs,Pi.sub_apply,rowBids,Fin.cons_zero] using
      norm_le_pi_norm (rowBids beta y omega-rowBids beta x omega) 0

theorem rowScore_decrease (hn : 2≤n) (hc : 1≤c) (hcR : c≤R)
    {V : Type*} {w0 w eps eta : ℝ} (hw0 : 0<w0)
    (heps : eps<referenceBid n R c w0)
    (hp : ∀b∈bidBox (ι:=Fin (R+1)) (referenceBid n R c w0-eps)
      (referenceBid n R c w0+eps),∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1)
    (hd : ∀b∈bidBox (ι:=Fin (R+1)) (referenceBid n R c w0-eps)
      (referenceBid n R c w0+eps),
      ‖fderiv ℝ (profileScore n c w) b-
        fderiv ℝ (profileScore n c w0) (fun _=>referenceBid n R c w0)‖≤eta)
    (beta : V→ℝ) (hbeta : ∀v,beta v∈Icc (referenceBid n R c w0-eps) (referenceBid n R c w0+eps))
    (x y : ℝ) (hx : x∈Icc (referenceBid n R c w0-eps) (referenceBid n R c w0+eps))
    (hy : y∈Icc (referenceBid n R c w0-eps) (referenceBid n R c w0+eps))
    (hxy : x≤y) (omega : Fin R→V) :
    (referenceCurvature n R (density R c) w0 (referenceBid n R c w0)-eta)*(y-x)≤
      finiteRowScore n c beta w x omega-finiteRowScore n c beta w y omega := by
  let B := referenceBid n R c w0
  have hlow : 0<B-eps := sub_pos.mpr heps
  have hbox (z : ℝ) (hz : z∈Icc (B-eps) (B+eps)) :
      rowBids beta z omega∈bidBox (B-eps) (B+eps) := by
    intro i
    refine Fin.cases hz (fun j=>hbeta (omega j)) i
  have hpos : ∀v,0<beta v := fun v=>hlow.trans_le (hbeta v).1
  have hrem := profileScore_increment_error hn (by omega) hlow hp hd
    (rowBids beta x omega) (rowBids beta y omega) (hbox x hx) (hbox y hy)
  have hlin := (source_reference_linearization hn hc hcR hw0
    (rowBids beta y omega-rowBids beta x omega)).2
  have he : fderiv ℝ (profileScore n c w0) (fun _ : Fin (R+1)=>B)
      (rowBids beta y omega-rowBids beta x omega)=
      -referenceCurvature n R (density R c) w0 B*(y-x) := by
    simpa only [rowBids,Pi.sub_apply,Fin.cons_zero,Fin.cons_succ,sub_self,
      Finset.sum_const_zero,mul_zero,add_zero] using hlin
  rw [he,norm_rowBids_sub_same,abs_of_nonneg (sub_nonneg.mpr hxy)] at hrem
  rw [finiteRowScore_eq_profileScore hn (by omega) beta w x omega
      (hlow.trans_le hx.1) hpos (hp _ (hbox x hx)),
    finiteRowScore_eq_profileScore hn (by omega) beta w y omega
      (hlow.trans_le hy.1) hpos (hp _ (hbox y hy))]
  have hh := (abs_le.mp hrem).2
  change (referenceCurvature n R (density R c) w0 B-eta)*(y-x)≤_
  nlinarith

private theorem averaged_sum_bound {D : ℝ} (_hD : 0≤D) (hR : 0<R)
    (h : Fin R→ℝ) (hh : ∀j,|h j|≤D) : |(∑j,h j)/(R:ℝ)|≤D := by
  have hRreal : (0:ℝ)<R := by exact_mod_cast hR
  rw [abs_div,abs_of_pos hRreal]
  apply (div_le_iff₀ hRreal).mpr
  calc
    _≤∑j,|h j| := Finset.abs_sum_le_sum_abs _ _
    _≤∑_j : Fin R,D := Finset.sum_le_sum (fun j _=>hh j)
    _=_ := by simp [mul_comm]

theorem profileScore_rival_bound (hn : 2≤n) (hc : 1≤c) (hcR : c≤R)
    {w0 w eps eta D : ℝ} (hw0 : 0<w0) (hD : 0≤D) (heta : 0≤eta)
    (heps : eps<referenceBid n R c w0)
    (hp : ∀b∈bidBox (ι:=Fin (R+1)) (referenceBid n R c w0-eps)
      (referenceBid n R c w0+eps),∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1)
    (hd : ∀b∈bidBox (ι:=Fin (R+1)) (referenceBid n R c w0-eps)
      (referenceBid n R c w0+eps),
      ‖fderiv ℝ (profileScore n c w) b-
        fderiv ℝ (profileScore n c w0) (fun _=>referenceBid n R c w0)‖≤eta)
    (a b : Fin (R+1)→ℝ)
    (ha : a∈bidBox (referenceBid n R c w0-eps) (referenceBid n R c w0+eps))
    (hb : b∈bidBox (referenceBid n R c w0-eps) (referenceBid n R c w0+eps))
    (hzero : b 0=a 0) (hab : ∀i,|b i-a i|≤D) :
    |profileScore n c w b-profileScore n c w a|≤
      (|referenceCurvature n R (density R c) w0 (referenceBid n R c w0)-
        referenceCommonSensitivity n R (density R c) w0 (referenceBid n R c w0)|+eta)*D := by
  let B := referenceBid n R c w0
  let A := referenceCurvature n R (density R c) w0 B
  let E := referenceCommonSensitivity n R (density R c) w0 B
  let L := fderiv ℝ (profileScore n c w0) (fun _ : Fin (R+1)=>B)
  have hnorm : ‖b-a‖≤D := (pi_norm_le_iff_of_nonneg hD).mpr (by
    intro i; simpa only [Real.norm_eq_abs,Pi.sub_apply] using hab i)
  have hrem := (profileScore_increment_error hn (by omega) (sub_pos.mpr heps) hp hd a b ha hb).trans
    (mul_le_mul_of_nonneg_left hnorm heta)
  have hlin : L (b-a)=(A-E)*((∑j : Fin R,(b j.succ-a j.succ))/(R:ℝ)) := by
    have hh := (source_reference_linearization hn hc hcR hw0 (b-a)).2
    simp only [Pi.sub_apply,hzero,sub_self,mul_zero,zero_add] at hh
    change L (b-a)=(A-E)/(R:ℝ)*(∑j : Fin R,(b j.succ-a j.succ)) at hh
    rw [hh]
    ring
  have hL : |L (b-a)|≤|A-E| *D := by
    rw [hlin,abs_mul]
    exact mul_le_mul_of_nonneg_left
      (averaged_sum_bound hD (by omega) (fun j=>b j.succ-a j.succ) (fun j=>hab j.succ)) (abs_nonneg _)
  change |profileScore n c w b-profileScore n c w a|≤(|A-E|+eta)*D
  calc
    _=|(profileScore n c w b-profileScore n c w a-L (b-a))+L (b-a)| := by congr 1; ring
    _≤|profileScore n c w b-profileScore n c w a-L (b-a)|+|L (b-a)| := abs_add_le _ _
    _≤eta*D+|A-E| *D := add_le_add hrem hL
    _=_ := by ring

end FCAppendix.Existence.NarrowPayOnce
