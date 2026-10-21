import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace FCAppendix.Affine.Uniform07
open scoped BigOperators
structure Box where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq
namespace Box
 def Holds (a : Box) (x : ℝ) : Prop := (a.lo:ℝ) ≤ x ∧ x ≤ (a.hi:ℝ)
 def point (q : ℚ) : Box := ⟨q,q⟩
 def add (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩
 def neg (a : Box) : Box := ⟨-a.hi,-a.lo⟩
 def sub (a b : Box) : Box := add a (neg b)
 def mul (a b : Box) : Box :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
 def scale (r : ℚ) (a : Box) : Box := mul (point r) a
 def inv (a : Box) : Box := ⟨a.hi⁻¹,a.lo⁻¹⟩
 def div (a b : Box) : Box := mul a (inv b)
 def inflate (a : Box) (e : ℚ) : Box := ⟨a.lo-e,a.hi+e⟩
 def sum {ι : Type*} (s : Finset ι) (a : ι → Box) : Box :=
  ⟨∑ i ∈ s, (a i).lo, ∑ i ∈ s, (a i).hi⟩
 theorem point_ok (r : ℚ) : (point r).Holds (r:ℝ) := ⟨le_rfl,le_rfl⟩
 theorem add_ok {a b : Box} {x y : ℝ} (hx : a.Holds x) (hy : b.Holds y) :
    (add a b).Holds (x+y) := by
  dsimp [Holds,add] at *; push_cast; constructor <;> linarith
 theorem neg_ok {a : Box} {x : ℝ} (hx : a.Holds x) : (neg a).Holds (-x) := by
  dsimp [Holds,neg] at *; push_cast; constructor <;> linarith
 theorem sub_ok {a b : Box} {x y : ℝ} (hx : a.Holds x) (hy : b.Holds y) :
    (sub a b).Holds (x-y) := by simpa [sub,sub_eq_add_neg] using add_ok hx (neg_ok hy)
 private theorem corners {al ah bl bh x y : ℝ}
    (hx : al ≤ x ∧ x ≤ ah) (hy : bl ≤ y ∧ y ≤ bh) :
    min (min (al*bl) (al*bh)) (min (ah*bl) (ah*bh)) ≤ x*y ∧
    x*y ≤ max (max (al*bl) (al*bh)) (max (ah*bl) (ah*bh)) := by
  have f (u v w r : ℝ) (hw : u ≤ w ∧ w ≤ v) :
      min (u*r) (v*r) ≤ w*r ∧ w*r ≤ max (u*r) (v*r) := by
    by_cases hr : 0 ≤ r
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hw.1 hr),
        (mul_le_mul_of_nonneg_right hw.2 hr).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hw.2 (le_of_not_ge hr)),
        (mul_le_mul_of_nonpos_right hw.1 (le_of_not_ge hr)).trans (le_max_left _ _)⟩
  have h0 := f al ah x y hx
  have h1 := f bl bh y al hy
  have h2 := f bl bh y ah hy
  simp only [mul_comm bl al,mul_comm bh al,mul_comm y al] at h1
  simp only [mul_comm bl ah,mul_comm bh ah,mul_comm y ah] at h2
  exact ⟨(min_le_min h1.1 h2.1).trans h0.1,h0.2.trans (max_le_max h1.2 h2.2)⟩
 theorem mul_ok {a b : Box} {x y : ℝ} (hx : a.Holds x) (hy : b.Holds y) :
    (mul a b).Holds (x*y) := by simpa [Holds,mul] using corners hx hy
 theorem scale_ok {a : Box} {x : ℝ} (r : ℚ) (hx : a.Holds x) :
    (scale r a).Holds ((r:ℝ)*x) := mul_ok (point_ok r) hx
 theorem inv_ok {a : Box} {x : ℝ} (ha : 0 < a.lo) (hx : a.Holds x) :
    (inv a).Holds x⁻¹ := by
  have hl : (0:ℝ) < a.lo := by exact_mod_cast ha
  constructor <;> dsimp [inv] <;> push_cast
  · exact inv_anti₀ (hl.trans_le hx.1) hx.2
  · exact inv_anti₀ hl hx.1
 theorem div_ok {a b : Box} {x y : ℝ} (hb : 0 < b.lo)
    (hx : a.Holds x) (hy : b.Holds y) : (div a b).Holds (x/y) := by
  simpa [div,div_eq_mul_inv] using mul_ok hx (inv_ok hb hy)
 theorem sum_ok {ι : Type*} (s : Finset ι) {a : ι → Box} {x : ι → ℝ}
    (h : ∀ i ∈ s, (a i).Holds (x i)) : (sum s a).Holds (∑ i ∈ s, x i) := by
  constructor <;> dsimp [sum] <;> push_cast
  · exact Finset.sum_le_sum (fun i hi => (h i hi).1)
  · exact Finset.sum_le_sum (fun i hi => (h i hi).2)
 theorem inflate_ok {a : Box} {x y : ℝ} {e : ℚ}
    (hx : a.Holds x) (he : |y-x| ≤ (e:ℝ)) : (inflate a e).Holds y := by
  have h := abs_le.mp he
  dsimp [Holds,inflate] at *; push_cast; constructor <;> linarith
 theorem widen {a b : Box} {x : ℝ} (hx : a.Holds x)
    (hl : b.lo ≤ a.lo) (hh : a.hi ≤ b.hi) : b.Holds x := by
  have hl' : (b.lo:ℝ) ≤ a.lo := by exact_mod_cast hl
  have hh' : (a.hi:ℝ) ≤ b.hi := by exact_mod_cast hh
  exact ⟨hl'.trans hx.1,hx.2.trans hh'⟩
 theorem lower {a : Box} {x : ℝ} {r : ℚ} (hx : a.Holds x) (h : r < a.lo) :
    (r:ℝ) < x := (by exact_mod_cast h : (r:ℝ) < a.lo).trans_le hx.1
 theorem upper {a : Box} {x : ℝ} {r : ℚ} (hx : a.Holds x) (h : a.hi < r) :
    x < (r:ℝ) := hx.2.trans_lt (by exact_mod_cast h)
 theorem lower_real {a : Box} {x r : ℝ} (hx : a.Holds x)
    (h : r < (a.lo:ℝ)) : r < x := h.trans_le hx.1
 theorem upper_real {a : Box} {x r : ℝ} (hx : a.Holds x)
    (h : (a.hi:ℝ) < r) : x < r := hx.2.trans_lt h
end Box

def expPolyQ (n : ℕ) (x : ℚ) : ℚ := ∑ j ∈ Finset.range n, x^j/(j.factorial:ℚ)
noncomputable def expPoly (n : ℕ) (x : ℝ) : ℝ := ∑ j ∈ Finset.range n, x^j/(j.factorial:ℝ)
@[simp] theorem expPoly_cast (n : ℕ) (x : ℚ) :
    (expPolyQ n x:ℝ) = expPoly n (x:ℝ) := by simp [expPolyQ,expPoly]

theorem expPoly_error (n : ℕ) {x s : ℝ} (_hs : 0 ≤ s) (hx : |x| ≤ s)
    (hsmall : s/(n+1:ℝ) ≤ 1/2) :
    |Real.exp x-expPoly n x| ≤ 2*s^n/(n.factorial:ℝ) := by
  have hc : ‖(x:ℂ)‖/(n+1:ℝ) ≤ 1/2 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using
      (div_le_div_of_nonneg_right hx (by positivity : (0:ℝ) ≤ n+1)).trans hsmall
  have hc' : ‖(x:ℂ)‖/(n.succ:ℝ) ≤ 1/2 := by simpa only [Nat.cast_succ] using hc
  have h := Complex.exp_bound' (n := n) hc'
  have hr : |Real.exp x-expPoly n x| ≤ |x|^n/(n.factorial:ℝ)*2 := by
    have ht : (∑ m ∈ Finset.range n, (x:ℂ)^m/(m.factorial:ℂ)) =
        (expPoly n x:ℂ) := by simp [expPoly]
    rw [ht, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  calc
    _ ≤ |x|^n/(n.factorial:ℝ)*2 := hr
    _ ≤ s^n/(n.factorial:ℝ)*2 := by gcongr
    _ = _ := by ring

def expErrorQ (n : ℕ) (s : ℚ) : ℚ := 2*s^n/(n.factorial:ℚ)
def expBox (n : ℕ) (x : ℚ) : Box :=
  Box.inflate (Box.point (expPolyQ n x)) (expErrorQ n |x|)
theorem expBox_ok (n : ℕ) (x : ℚ) (h : |x|/(n+1:ℚ) ≤ 1/2) :
    (expBox n x).Holds (Real.exp (x:ℝ)) := by
  apply Box.inflate_ok (Box.point_ok _)
  rw [expPoly_cast]
  have hcast : ((|x|/(n+1:ℚ):ℚ):ℝ) ≤ ((1/2:ℚ):ℝ) := by exact_mod_cast h
  have hsmall : |(x:ℝ)|/((n:ℝ)+1) ≤ 1/2 := by
    simpa only [Rat.cast_div, Rat.cast_abs, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_one, Rat.cast_ofNat] using hcast
  simpa [expErrorQ] using expPoly_error n (x := (x:ℝ))
    (abs_nonneg (x:ℝ)) le_rfl hsmall

structure LogCertificate (q : ℚ) where
  lo : ℚ
  hi : ℚ
  n : ℕ
  q_pos : 0 < q
  lo_small : |lo|/(n+1:ℚ) ≤ 1/2
  hi_small : |hi|/(n+1:ℚ) ≤ 1/2
  lower_check : (expBox n lo).hi < q
  upper_check : q < (expBox n hi).lo
namespace LogCertificate
 def box {q : ℚ} (c : LogCertificate q) : Box := ⟨c.lo,c.hi⟩
 theorem correct {q : ℚ} (c : LogCertificate q) : c.box.Holds (Real.log (q:ℝ)) := by
  have hq : (0:ℝ) < q := by exact_mod_cast c.q_pos
  have hl := Box.upper (expBox_ok c.n c.lo c.lo_small) c.lower_check
  have hh := Box.lower (expBox_ok c.n c.hi c.hi_small) c.upper_check
  have hl' : (c.lo:ℝ) < Real.log (q:ℝ) := by
    apply Real.exp_strictMono.lt_iff_lt.mp; simpa [Real.exp_log hq] using hl
  have hh' : Real.log (q:ℝ) < (c.hi:ℝ) := by
    apply Real.exp_strictMono.lt_iff_lt.mp; simpa [Real.exp_log hq] using hh
  exact ⟨hl'.le,hh'.le⟩
end LogCertificate

def logBox (a : Box) (cl : LogCertificate a.lo) (ch : LogCertificate a.hi) : Box := ⟨cl.lo,ch.hi⟩
theorem logBox_ok {a : Box} (cl : LogCertificate a.lo) (ch : LogCertificate a.hi)
    {x : ℝ} (hx : a.Holds x) : (logBox a cl ch).Holds (Real.log x) := by
  have hp : (0:ℝ) < a.lo := by exact_mod_cast cl.q_pos
  exact ⟨cl.correct.1.trans (Real.log_le_log hp hx.1),
    (Real.log_le_log (hp.trans_le hx.1) hx.2).trans ch.correct.2⟩
end FCAppendix.Affine.Uniform07
