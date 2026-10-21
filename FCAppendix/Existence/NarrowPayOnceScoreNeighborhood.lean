import FCAppendix.Existence.NarrowPayOnceThirdProfile
import FCAppendix.Existence.NarrowPayOnceProfileScore

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators ContDiff

section ScalarBounds
variable {E : Type*} [SeminormedAddCommGroup E]

structure ScalarControl (s : Set E) (f : E→ℝ) (B L : ℝ) : Prop where
  bound_nonneg : 0≤B
  rate_nonneg : 0≤L
  bound : ∀x∈s,|f x|≤B
  variation : ∀x∈s,∀y∈s,|f x-f y|≤L*‖x-y‖

namespace ScalarControl
variable {s : Set E} {f g : E→ℝ} {B L C M : ℝ}

theorem const {c B : ℝ} (hc : |c|≤B) : ScalarControl s (fun _=>c) B 0 := by
  refine ⟨(abs_nonneg _).trans hc,le_rfl,fun _ _=>hc,?_⟩
  intro x _ y _
  simp

theorem neg (hf : ScalarControl s f B L) : ScalarControl s (fun x=> -f x) B L := by
  refine ⟨hf.bound_nonneg,hf.rate_nonneg,?_,?_⟩
  · intro x hx; simpa only [abs_neg] using hf.bound x hx
  · intro x hx y hy
    simpa only [neg_sub_neg,abs_sub_comm] using hf.variation x hx y hy

theorem add (hf : ScalarControl s f B L) (hg : ScalarControl s g C M) :
    ScalarControl s (fun x=>f x+g x) (B+C) (L+M) := by
  refine ⟨add_nonneg hf.bound_nonneg hg.bound_nonneg,add_nonneg hf.rate_nonneg hg.rate_nonneg,?_,?_⟩
  · intro x hx
    exact (abs_add_le _ _).trans (add_le_add (hf.bound x hx) (hg.bound x hx))
  · intro x hx y hy
    have he : f x+g x-(f y+g y)=(f x-f y)+(g x-g y) := by ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add (hf.variation x hx y hy) (hg.variation x hx y hy)).trans
      (by ring_nf; exact le_rfl))

theorem sub (hf : ScalarControl s f B L) (hg : ScalarControl s g C M) :
    ScalarControl s (fun x=>f x-g x) (B+C) (L+M) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : ScalarControl s f B L) (hg : ScalarControl s g C M) :
    ScalarControl s (fun x=>f x*g x) (B*C) (B*M+L*C) := by
  refine ⟨mul_nonneg hf.bound_nonneg hg.bound_nonneg,
    add_nonneg (mul_nonneg hf.bound_nonneg hg.rate_nonneg)
      (mul_nonneg hf.rate_nonneg hg.bound_nonneg),?_,?_⟩
  · intro x hx
    rw [abs_mul]
    exact mul_le_mul (hf.bound x hx) (hg.bound x hx) (abs_nonneg _) hf.bound_nonneg
  · intro x hx y hy
    have he : f x*g x-f y*g y=f x*(g x-g y)+(f x-f y)*g y := by ring
    rw [he]
    calc
      _≤|f x| * |g x-g y|+|f x-f y| * |g y| := by
        simpa only [abs_mul] using abs_add_le (f x*(g x-g y)) ((f x-f y)*g y)
      _≤B*(M*‖x-y‖)+(L*‖x-y‖)*C :=
        add_le_add (mul_le_mul (hf.bound x hx) (hg.variation x hx y hy)
          (abs_nonneg _) hf.bound_nonneg)
          (mul_le_mul (hf.variation x hx y hy) (hg.bound y hy) (abs_nonneg _)
            (mul_nonneg hf.rate_nonneg (norm_nonneg _)))
      _=_ := by ring

theorem mono (hf : ScalarControl s f B L) {C M : ℝ} (hB : B≤C) (hL : L≤M) :
    ScalarControl s f C M := by
  refine ⟨hf.bound_nonneg.trans hB,hf.rate_nonneg.trans hL,
    fun x hx=>(hf.bound x hx).trans hB,?_⟩
  intro x hx y hy
  exact (hf.variation x hx y hy).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

theorem probability_pow {f : E→ℝ} {A : ℝ} (hA : 0≤A)
    (hrange : ∀x∈s,f x∈Icc (0:ℝ) 1)
    (hLip : ∀x∈s,∀y∈s,|f x-f y|≤A*‖x-y‖) (k : ℕ) :
    ScalarControl s (fun x=>(f x)^k) 1 ((k:ℝ)*A) := by
  refine ⟨zero_le_one,mul_nonneg (Nat.cast_nonneg _) hA,?_,?_⟩
  · intro x hx
    rw [abs_of_nonneg (pow_nonneg (hrange x hx).1 _)]
    exact pow_le_one₀ (hrange x hx).1 (hrange x hx).2
  · intro x hx y hy
    calc
      _≤|f x-f y| * (k:ℝ)*(max |f x| |f y|)^(k-1) := abs_pow_sub_pow_le ..
      _≤(A*‖x-y‖)*(k:ℝ)*1 := by
        gcongr
        · exact hLip x hx y hy
        · apply pow_le_one₀ (by positivity)
          rw [max_le_iff]
          exact ⟨by simpa only [abs_of_nonneg (hrange x hx).1] using (hrange x hx).2,
            by simpa only [abs_of_nonneg (hrange y hy).1] using (hrange y hy).2⟩
      _=_ := by ring

end ScalarControl
end ScalarBounds

variable {R n c : ℕ}

theorem norm_focalDirection (R : ℕ) : ‖focalDirection R‖=1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    refine Fin.cases ?_ (fun j=>?_) i <;> simp [focalDirection]
  · simpa [focalDirection] using norm_le_pi_norm (focalDirection R) 0

theorem kernel_profile_lipschitz (hn : 2≤n) (hc : c≤R+1)
    {lower upper : ℝ} (hlower : 0<lower)
    (hinterior : ∀b∈bidBox (ι:=Fin (R+1)) lower upper, ∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1)
    (a b : Fin (R+1)→ℝ) (ha : a∈bidBox lower upper) (hb : b∈bidBox lower upper) :
    ‖kernelMarginal n c b-kernelMarginal n c a‖≤firstJetBound n lower*‖b-a‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ)
    (s:=bidBox lower upper) ?_ ?_ (bidBox_convex lower upper) ha hb
  · intro d hd
    exact (contDiffAt_kernelMarginal_interior hn (by simpa using hc) d
      (fun i=>hlower.trans_le (hd i).1) (hinterior d hd)).differentiableAt (by simp)
  · intro d hd
    exact norm_fderiv_kernelMarginal_le hn (by simpa using hc) hlower d
      (fun i=>(hd i).1) (hinterior d hd)

def scoreJetRate (n : ℕ) (lower upper W : ℝ) : ℝ :=
  let A := firstJetBound n lower
  let B := secondJetBound n lower upper
  let C := thirdJetBound n lower upper
  2*(n:ℝ)*((n:ℝ)*A^2+B)+(n:ℝ)^2*(A^2+W*((n:ℝ)*A^3+2*A*B))+
    (n:ℝ)*(B+W*((n:ℝ)*A*B+C))

theorem profileScoreDerivative_lipschitz (hn : 2≤n) (hc : c≤R+1)
    {lower upper : ℝ} (hlower : 0<lower)
    (hinterior : ∀b∈bidBox (ι:=Fin (R+1)) lower upper, ∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1)
    (w : ℝ) (a b : Fin (R+1)→ℝ) (ha : a∈bidBox lower upper) (hb : b∈bidBox lower upper)
    (h : Fin (R+1)→ℝ) :
    |profileScoreDerivative n c w b h-profileScoreDerivative n c w a h|≤
      scoreJetRate n lower upper (|w|+upper)*‖h‖*‖b-a‖ := by
  let s := bidBox (ι:=Fin (R+1)) lower upper
  let K := kernelMarginal (ι:=Fin (R+1)) n c
  let e := focalDirection R
  let A := firstJetBound n lower
  let B := secondJetBound n lower upper
  let C := thirdJetBound n lower upper
  let W := |w|+upper
  have hupper : 0≤upper := (hlower.trans_le (ha 0).1).le.trans (ha 0).2
  have hA : 0≤A := by dsimp [A,firstJetBound]; positivity
  have hB : 0≤B := by dsimp [B,secondJetBound,firstJetBound]; positivity
  have hC : 0≤C := by dsimp [C,thirdJetBound,secondJetBound,firstJetBound]; positivity
  have hp (x : Fin (R+1)→ℝ) (hx : x∈s) : K x 0∈Icc (0:ℝ) 1 :=
    ⟨(hinterior x hx 0).1.le,(hinterior x hx 0).2.le⟩
  have hpow (k : ℕ) (hk : k≤n) :
      ScalarControl s (fun x=>(1-K x 0)^k) 1 ((n:ℝ)*A) := by
    apply (ScalarControl.probability_pow hA (fun x hx=>?_) (fun x hx y hy=>?_) k).mono le_rfl
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hA)
    · exact ⟨by linarith [(hp x hx).2],by linarith [(hp x hx).1]⟩
    · have hi : |K x 0-K y 0|≤‖K x-K y‖ := by
        simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (K x-K y) 0
      have hh := kernel_profile_lipschitz hn hc hlower hinterior y x hy hx
      simpa only [sub_sub_sub_cancel_left,abs_sub_comm] using hi.trans hh
  have hfirst (z : Fin (R+1)→ℝ) :
      ScalarControl s (fun x=>fderiv ℝ K x z 0) (A*‖z‖) (B*‖z‖) := by
    refine ⟨mul_nonneg hA (norm_nonneg _),mul_nonneg hB (norm_nonneg _),?_,?_⟩
    · intro x hx
      have hi : |fderiv ℝ K x z 0|≤‖fderiv ℝ K x z‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fderiv ℝ K x z) 0
      exact hi.trans (((fderiv ℝ K x).le_opNorm z).trans (mul_le_mul_of_nonneg_right
        (norm_fderiv_kernelMarginal_le hn (by simpa using hc) hlower x (fun i=>(hx i).1)
          (hinterior x hx)) (norm_nonneg _)))
    · intro x hx y hy
      have hi : |fderiv ℝ K x z 0-fderiv ℝ K y z 0|≤‖fderiv ℝ K x z-fderiv ℝ K y z‖ := by
        simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (fderiv ℝ K x z-fderiv ℝ K y z) 0
      exact hi.trans (first_kernel_jet_lipschitz hn (by simpa using hc) hlower hinterior y x hy hx z)
  have he : ScalarControl s (fun x=>fderiv ℝ K x e 0) A B := by
    simpa only [e,norm_focalDirection,mul_one] using hfirst e
  have hsecond : ScalarControl s
      (fun x=>fderiv ℝ (fun y=>fderiv ℝ K y e) x h 0) (B*‖h‖) (C*‖h‖) := by
    refine ⟨mul_nonneg hB (norm_nonneg _),mul_nonneg hC (norm_nonneg _),?_,?_⟩
    · intro x hx
      have hi : |fderiv ℝ (fun y=>fderiv ℝ K y e) x h 0|≤‖fderiv ℝ (fun y=>fderiv ℝ K y e) x h‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fderiv ℝ (fun y=>fderiv ℝ K y e) x h) 0
      exact hi.trans (by simpa only [e,norm_focalDirection,mul_one,B,secondJetBound,firstJetBound,K] using
        norm_fderiv_fderiv_kernelMarginal_le hn (by simpa using hc) hlower x hx (hinterior x hx) e h)
    · intro x hx y hy
      have hi : |fderiv ℝ (fun z=>fderiv ℝ K z e) x h 0-fderiv ℝ (fun z=>fderiv ℝ K z e) y h 0|≤
          ‖fderiv ℝ (fun z=>fderiv ℝ K z e) x h-fderiv ℝ (fun z=>fderiv ℝ K z e) y h‖ := by
        simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm
          (fderiv ℝ (fun z=>fderiv ℝ K z e) x h-fderiv ℝ (fun z=>fderiv ℝ K z e) y h) 0
      exact hi.trans (by simpa only [e,norm_focalDirection,mul_one] using
        second_kernel_jet_lipschitz hn (by simpa using hc) hlower hinterior y x hy hx e h)
  have ht : ScalarControl s (fun x=>w-x 0) W 1 := by
    refine ⟨by dsimp [W]; positivity,zero_le_one,?_,?_⟩
    · intro x hx
      exact (abs_sub _ _).trans (add_le_add le_rfl
        (show |x 0|≤upper by rw [abs_of_pos (hlower.trans_le (hx 0).1)]; exact (hx 0).2))
    · intro x hx y hy
      have hi : |x 0-y 0|≤‖x-y‖ := by
        simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (x-y) 0
      simpa only [sub_sub_sub_cancel_left,abs_sub_comm,one_mul] using hi
  have hnconst : ScalarControl s (fun _=>(n:ℝ)) n 0 := ScalarControl.const (by simp)
  have hpred : ScalarControl s (fun _=>((n-1:ℕ):ℝ)) n 0 :=
    ScalarControl.const (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast Nat.sub_le n 1)
  have hhconst : ScalarControl s (fun _=>h 0) ‖h‖ 0 := ScalarControl.const
    (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm h 0)
  have h1 := ((hhconst.neg.mul hnconst).mul (hpow (n-1) (Nat.sub_le _ _))).mul he
  have h2 := (((((ht.mul hnconst).mul hpred).mul (hpow (n-2) (Nat.sub_le _ _))).mul (hfirst h)).mul he)
  have h3 := ((ht.mul hnconst).mul (hpow (n-1) (Nat.sub_le _ _))).mul hsecond
  have h4 := (hnconst.mul (hpow (n-1) (Nat.sub_le _ _))).mul (hfirst h)
  have hout := ((h1.sub h2).add h3).sub h4
  have hh := hout.variation b hb a ha
  change |profileScoreDerivative n c w b h-profileScoreDerivative n c w a h|≤_ at hh
  convert hh using 1
  dsimp [scoreJetRate,A,B,C,W]
  ring

theorem norm_fderiv_profileScore_sub_le (hn : 2≤n) (hc : c≤R+1)
    {lower upper : ℝ} (hlower : 0<lower)
    (hinterior : ∀b∈bidBox (ι:=Fin (R+1)) lower upper, ∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1)
    (w : ℝ) (a b : Fin (R+1)→ℝ) (ha : a∈bidBox lower upper) (hb : b∈bidBox lower upper) :
    ‖fderiv ℝ (profileScore n c w) b-fderiv ℝ (profileScore n c w) a‖≤
      scoreJetRate n lower upper (|w|+upper)*‖b-a‖ := by
  have hupper : 0≤upper := (hlower.trans_le (ha 0).1).le.trans (ha 0).2
  have hC : 0 ≤ scoreJetRate n lower upper (|w|+upper) := by
    unfold scoreJetRate thirdJetBound secondJetBound firstJetBound
    positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro h
  rw [Real.norm_eq_abs,sub_apply,
    fderiv_profileScore hn hc w b (fun i=>hlower.trans_le (hb i).1) (hinterior b hb) h,
    fderiv_profileScore hn hc w a (fun i=>hlower.trans_le (ha i).1) (hinterior a ha) h]
  convert profileScoreDerivative_lipschitz hn hc hlower hinterior w a b ha hb h using 1
  ring

theorem firstJetBound_mono (n : ℕ) {lo lo' : ℝ} (hlo : 0<lo) (hlower : lo≤lo') :
    firstJetBound n lo'≤firstJetBound n lo := by
  exact div_le_div_of_nonneg_left (by positivity) hlo hlower

theorem secondJetBound_mono (n : ℕ) {lo lo' hi hi' : ℝ} (hlo : 0<lo)
    (hlower : lo≤lo') (hhi : 0≤hi') (hupper : hi'≤hi) :
    secondJetBound n lo' hi' ≤ secondJetBound n lo hi := by
  have hlo' : 0<lo' := hlo.trans_le hlower
  have hA := firstJetBound_mono n hlo hlower
  have hA0 : 0≤firstJetBound n lo' := by unfold firstJetBound; positivity
  have hA1 : 0≤firstJetBound n lo := hA0.trans hA
  have hhi1 : 0≤hi := hhi.trans hupper
  unfold secondJetBound
  gcongr

theorem thirdJetBound_mono (n : ℕ) {lo lo' hi hi' : ℝ} (hlo : 0<lo)
    (hlower : lo≤lo') (hhi : 0≤hi') (hupper : hi'≤hi) :
    thirdJetBound n lo' hi'≤thirdJetBound n lo hi := by
  have hlo' : 0<lo' := hlo.trans_le hlower
  have hA := firstJetBound_mono n hlo hlower
  have hB := secondJetBound_mono n hlo hlower hhi hupper
  have hA0 : 0≤firstJetBound n lo' := by unfold firstJetBound; positivity
  have hB0 : 0 ≤ secondJetBound n lo' hi' := by unfold secondJetBound firstJetBound; positivity
  have hA1 : 0≤firstJetBound n lo := hA0.trans hA
  have hB1 : 0 ≤ secondJetBound n lo hi := hB0.trans hB
  have hhi1 : 0≤hi := hhi.trans hupper
  dsimp [thirdJetBound]
  gcongr

theorem scoreJetRate_mono (n : ℕ) {lo lo' hi hi' W W' : ℝ} (hlo : 0<lo)
    (hlower : lo≤lo') (hhi : 0≤hi') (hupper : hi'≤hi) (hW : 0≤W') (hWW : W'≤W) :
    scoreJetRate n lo' hi' W' ≤ scoreJetRate n lo hi W := by
  have hlo' : 0<lo' := hlo.trans_le hlower
  have hA := firstJetBound_mono n hlo hlower
  have hB := secondJetBound_mono n hlo hlower hhi hupper
  have hC := thirdJetBound_mono n hlo hlower hhi hupper
  have hA0 : 0≤firstJetBound n lo' := by unfold firstJetBound; positivity
  have hB0 : 0 ≤ secondJetBound n lo' hi' := by unfold secondJetBound firstJetBound; positivity
  have hC0 : 0≤thirdJetBound n lo' hi' := by unfold thirdJetBound secondJetBound firstJetBound; positivity
  have hA1 : 0≤firstJetBound n lo := hA0.trans hA
  have hB1 : 0 ≤ secondJetBound n lo hi := hB0.trans hB
  have hC1 : 0≤thirdJetBound n lo hi := hC0.trans hC
  have hW1 : 0≤W := hW.trans hWW
  dsimp [scoreJetRate]
  gcongr

def scoreTypeJetBound (n : ℕ) (lower upper : ℝ) : ℝ :=
  (n:ℝ)^2*(firstJetBound n lower)^2+(n:ℝ)*secondJetBound n lower upper

theorem norm_fderiv_profileScore_type_sub_le (hn : 2≤n) (hc : c≤R+1)
    {lower upper : ℝ} (hlower : 0<lower) (b : Fin (R+1)→ℝ)
    (hb : b∈bidBox lower upper) (hp : ∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1)
    (w v : ℝ) : ‖fderiv ℝ (profileScore n c w) b-fderiv ℝ (profileScore n c v) b‖≤
      scoreTypeJetBound n lower upper*|w-v| := by
  let K := kernelMarginal (ι:=Fin (R+1)) n c
  let p := K b 0
  let e := focalDirection R
  let A := firstJetBound n lower
  let B := secondJetBound n lower upper
  have hupper : 0≤upper := (hlower.trans_le (hb 0).1).le.trans (hb 0).2
  have hA : 0≤A := by dsimp [A,firstJetBound]; positivity
  have hB : 0≤B := by dsimp [B,secondJetBound,firstJetBound]; positivity
  have hC : 0 ≤ scoreTypeJetBound n lower upper := by unfold scoreTypeJetBound secondJetBound firstJetBound; positivity
  have hpow (k : ℕ) : 0≤(1-p)^k ∧ (1-p)^k≤1 :=
    ⟨pow_nonneg (by dsimp [p,K]; linarith [(hp 0).2]) _,
      pow_le_one₀ (by dsimp [p,K]; linarith [(hp 0).2]) (by dsimp [p,K]; linarith [(hp 0).1])⟩
  have hfirst (z : Fin (R+1)→ℝ) : |fderiv ℝ K b z 0|≤A*‖z‖ := by
    have hi : |fderiv ℝ K b z 0|≤‖fderiv ℝ K b z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fderiv ℝ K b z) 0
    exact hi.trans (((fderiv ℝ K b).le_opNorm z).trans (mul_le_mul_of_nonneg_right
      (norm_fderiv_kernelMarginal_le hn (by simpa using hc) hlower b (fun i=>(hb i).1) hp) (norm_nonneg _)))
  have he : |fderiv ℝ K b e 0|≤A := by simpa only [e,norm_focalDirection,mul_one] using hfirst e
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (abs_nonneg _))
  intro h
  rw [Real.norm_eq_abs,sub_apply,
    fderiv_profileScore hn hc w b (fun i=>hlower.trans_le (hb i).1) hp h,
    fderiv_profileScore hn hc v b (fun i=>hlower.trans_le (hb i).1) hp h]
  have hsecond : |fderiv ℝ (fun y=>fderiv ℝ K y e) b h 0|≤B*‖h‖ := by
    have hi : |fderiv ℝ (fun y=>fderiv ℝ K y e) b h 0|≤‖fderiv ℝ (fun y=>fderiv ℝ K y e) b h‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fderiv ℝ (fun y=>fderiv ℝ K y e) b h) 0
    exact hi.trans (by simpa only [e,norm_focalDirection,mul_one,B,secondJetBound,firstJetBound,K] using
      norm_fderiv_fderiv_kernelMarginal_le hn (by simpa using hc) hlower b hb hp e h)
  have hpred : 0≤((n-1:ℕ):ℝ) := Nat.cast_nonneg _
  have hpredle : ((n-1:ℕ):ℝ)≤n := by exact_mod_cast Nat.sub_le n 1
  have hinner : |-((n-1:ℕ):ℝ)*(1-p)^(n-2)*fderiv ℝ K b h 0*fderiv ℝ K b e 0+
      (1-p)^(n-1)*fderiv ℝ (fun y=>fderiv ℝ K y e) b h 0|≤
      (n:ℝ)*A^2*‖h‖+B*‖h‖ := by
    calc
      _≤|((n-1:ℕ):ℝ)*(1-p)^(n-2)*fderiv ℝ K b h 0*fderiv ℝ K b e 0|+
        |(1-p)^(n-1)*fderiv ℝ (fun y=>fderiv ℝ K y e) b h 0| := by
        simpa only [neg_mul,abs_neg] using abs_add_le
          (-(((n-1:ℕ):ℝ)*(1-p)^(n-2)*fderiv ℝ K b h 0*fderiv ℝ K b e 0))
          ((1-p)^(n-1)*fderiv ℝ (fun y=>fderiv ℝ K y e) b h 0)
      _=((n-1:ℕ):ℝ)*(1-p)^(n-2)*|fderiv ℝ K b h 0| * |fderiv ℝ K b e 0|+
        (1-p)^(n-1)*|fderiv ℝ (fun y=>fderiv ℝ K y e) b h 0| := by
        simp only [abs_mul,abs_of_nonneg hpred,abs_of_nonneg (hpow _).1]
      _≤(n:ℝ)*1*(A*‖h‖)*A+1*(B*‖h‖) := by
        gcongr <;> first | exact (hpow _).1 | exact (hpow _).2 | exact hfirst h
      _=_ := by ring
  have heq : profileScoreDerivative n c w b h-profileScoreDerivative n c v b h=
      (w-v)*(n:ℝ)*(-((n-1:ℕ):ℝ)*(1-p)^(n-2)*fderiv ℝ K b h 0*fderiv ℝ K b e 0+
        (1-p)^(n-1)*fderiv ℝ (fun y=>fderiv ℝ K y e) b h 0) := by
    dsimp [profileScoreDerivative,p,K,e]
    ring
  have hnabs : |(n:ℝ)|=(n:ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  rw [heq,abs_mul,abs_mul,hnabs]
  calc
    _≤(|w-v| * (n:ℝ))*((n:ℝ)*A^2*‖h‖+B*‖h‖) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _=_ := by dsimp [scoreTypeJetBound,A,B]; ring

end FCAppendix.Existence.NarrowPayOnce
