import Std

namespace Lupanov

/-- A dyadic square-root scale gives the error term of (8.3). Multiplying
through by `n*d` avoids division and rounding. One may take d = ⌊√n⌋. -/
theorem parameters (n d : Nat) (hn : 1024 ≤ n) (hd : d*d ≤ n) :
    ∃ m p s r : Nat, n = m+p+r ∧ 0<s ∧ 2^m ≤ p*s ∧
      n*d*((p+2)*2^(p+r)+(p*2^s+1)*2^(m+p+1)) ≤ (d+200)*2^n := by
  let k := n.log2 / 2
  let t := 2^k
  let m := k+k+k
  have hn' : n ≠ 0 := by omega
  have hk : 5 ≤ k := by
    have := (Nat.le_log2 hn').mpr (show 2^10 ≤ n from hn)
    dsimp [k]; omega
  have ht : 32 ≤ t := Nat.pow_le_pow_right (n := 2) (by decide) hk
  have hkt : k ≤ t := Nat.le_of_lt Nat.lt_two_pow_self
  have hl : t*t ≤ n := calc
    _ = 2^(k+k) := (Nat.pow_add ..).symm
    _ ≤ 2^n.log2 := Nat.pow_le_pow_right (n := 2) (by decide) (by dsimp [k]; omega)
    _ ≤ n := Nat.log2_self_le hn'
  have hu : n < 4*(t*t) := calc
    _ < 2^(n.log2+1) := Nat.lt_log2_self
    _ ≤ 2^((k+k)+2) := Nat.pow_le_pow_right (n := 2) (by decide) (by dsimp [k]; omega)
    _ = _ := by simp only [Nat.pow_add]; dsimp [t]; grind
  have hd' : d ≤ 2*t := by
    apply Nat.le_of_not_lt; intro h
    have H := Nat.mul_le_mul (show 2*t ≤ d by omega) (show 2*t ≤ d by omega)
    grind
  let s := n-16*t
  have h32 := Nat.mul_le_mul_right t ht
  have hs : 0<s := by dsimp [s]; omega
  have hsum : s+16*t=n := by dsimp [s]; omega
  have hhalf : t*t ≤ 2*s := by omega
  have hm : 2^m = t*t*t := by simp only [m, Nat.pow_add, t]
  -- Since the row count is positive, this is its ceiling quotient by s.
  let p := (2^m - 1) / s + 1
  have cover : 2^m ≤ p*s := by
    have H := Nat.lt_mul_div_succ (2^m - 1) hs
    rw [Nat.mul_comm] at H
    dsimp [p]; omega
  have floorBound : p*s ≤ 2^m+s := by
    have H := Nat.div_mul_le_self (2^m - 1) s
    simp only [p, Nat.add_mul, Nat.one_mul]; omega
  have hp : p ≤ 2*t+1 := by
    have H := Nat.mul_le_mul_right t hhalf
    have H' : 2^m < (2*t+1)*s := by rw [hm]; grind
    have := (Nat.div_lt_iff_lt_mul hs).mpr (show 2^m-1 < (2*t+1)*s by omega)
    dsimp [p]; omega
  have hqr : m+p ≤ n := by dsimp [m]; omega
  let r := n-(m+p)
  have split : n=m+p+r := by dsimp [r]; omega
  refine ⟨m,p,s,r,split,hs,cover,?_⟩
  have hpow : 2^n = 2^m*2^(p+r) := by
    rw [show n=m+(p+r) by omega, Nat.pow_add]
  -- Charge the p stars and two decoder contacts per suffix to the leading term.
  have hpCost : n*(p+2) ≤ 2^m+60*(t*t) := by
    have H := Nat.mul_le_mul_left t hp
    have H' := congrArg (· * p) hsum
    have Ht := Nat.mul_le_mul_right t (show 1 ≤ t by omega)
    grind
  have hmain : n*d*(p+2) ≤ (d+120)*2^m := by
    have H := Nat.mul_le_mul_right d hpCost
    have H' := Nat.mul_le_mul_left (t*t) hd'
    rw [hm] at H ⊢
    grind
  have hmain' := Nat.mul_le_mul_right (2^(p+r)) hmain
  -- The library overhead fits inside one extra copy of 2^n after scaling.
  have hscale : n*d ≤ 2^(m+3) := by
    have H := Nat.mul_le_mul (Nat.le_of_lt hu) hd'
    rw [Nat.pow_add, hm]; grind
  have hmask : p*2^s+1 ≤ 2^(k+2+s) := by
    have H := Nat.mul_le_mul_right (2^s) (show p+1 ≤ 4*t by omega)
    have H' := Nat.two_pow_pos s
    rw [Nat.pow_add, Nat.pow_add 2 k 2]; change _ ≤ (t*4)*2^s
    grind
  have htail : n*d*((p*2^s+1)*2^(m+p+1)) ≤ 2^n := calc
    _ ≤ 2^(m+3)*(2^(k+2+s)*2^(m+p+1)) :=
      Nat.mul_le_mul hscale (Nat.mul_le_mul_right _ hmask)
    _ = 2^((m+3)+((k+2+s)+(m+p+1))) := by simp only [Nat.pow_add, Nat.mul_assoc]
    _ ≤ _ := Nat.pow_le_pow_right (n := 2) (by decide) (by dsimp [m]; omega)
  have H : n*d*((p+2)*2^(p+r)) ≤ (d+120)*2^n := by
    simpa only [hpow, Nat.mul_assoc] using hmain'
  rw [Nat.mul_add]
  have sum := Nat.add_le_add H htail
  grind

end Lupanov
