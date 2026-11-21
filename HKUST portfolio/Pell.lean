import Mathlib

def Pell_sol (d x y : ℤ) : Prop :=
  x ^ 2 - d * y ^ 2 = 1
theorem pell_2_example :
    Pell_sol 2 3 2 := by
  unfold Pell_sol
  norm_num
def pellMul (d : ℤ) (a b : ℤ × ℤ) : ℤ × ℤ :=
  (a.1 * b.1 + d * a.2 * b.2,
   a.1 * b.2 + a.2 * b.1)
def pellSeq (d : ℤ) (base : ℤ × ℤ) :
    ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => pellMul d (pellSeq d base n) base
theorem pell_one_zero (d : ℤ) :
    Pell_sol d 1 0 := by
  unfold Pell_sol
  ring
theorem pellMul_correct
    (d : ℤ) (a b : ℤ × ℤ)
    (ha : Pell_sol d a.1 a.2)
    (hb : Pell_sol d b.1 b.2) :
    Pell_sol d
      (pellMul d a b).1
      (pellMul d a b).2 := by
  unfold Pell_sol at *
  unfold pellMul
  dsimp
  calc
    (a.1 * b.1 + d * a.2 * b.2)^2
      - d * (a.1 * b.2 + a.2 * b.1)^2
        = (a.1^2 - d * a.2^2) *
          (b.1^2 - d * b.2^2) := by ring
    _ = 1 := by
      rw [ha, hb]
      norm_num
theorem pellSeq_correct
    (d : ℤ) (base : ℤ × ℤ)
    (hbase : Pell_sol d base.1 base.2)
    (n : ℕ) :
    Pell_sol d
      (pellSeq d base n).1
      (pellSeq d base n).2 := by
      induction n with
  | zero =>
    exact pell_one_zero d
  | succ k ih =>
      exact pellMul_correct d (pellSeq d base k) base ih hbase
theorem pellSeq_positive
    (d : ℤ) (base : ℤ × ℤ)
    (hd : 0 < d)
    (hx : 1 < base.1)
    (hy : 0 < base.2)
    (n : ℕ) :
    1 ≤ (pellSeq d base n).1 ∧
    0 ≤ (pellSeq d base n).2 := by
      induction n with
  | zero =>
      simp [pellSeq]
  | succ k ih =>
      obtain ⟨ihx, ihy⟩ := ih
      simp only [pellSeq, pellMul]
      constructor
      ·
        have h₁ : 0 ≤ (pellSeq d base k).2 * base.2 := by
          exact mul_nonneg ihy (le_of_lt hy)
        have h₂ : 0 ≤ d * ((pellSeq d base k).2 * base.2) := by
          exact mul_nonneg (le_of_lt hd) h₁
        have hbx : 0 ≤ base.1 := by omega
        nlinarith [mul_nonneg (sub_nonneg.mpr ihx) hbx]
      ·
        have hbx : 0 ≤ base.1 := by omega
        nlinarith [mul_nonneg ihy hbx,
                   mul_nonneg (le_trans (by omega : 0 ≤ (1 : ℤ)) ihx) (le_of_lt hy)]
theorem pellSeq_strictIncrease
    (d : ℤ) (base : ℤ × ℤ)
    (hd : 0 < d)
    (hx : 1 < base.1)
    (hy : 0 < base.2)
    (n : ℕ) :
    (pellSeq d base n).1 <
    (pellSeq d base (n + 1)).1 := by
  obtain ⟨ihx, ihy⟩ :=
    pellSeq_positive d base hd hx hy n

  have h₁ : 0 < (pellSeq d base n).1 := by
    omega

  have h₂ : 0 < base.1 - 1 := by
    omega

  have h₃ :
      0 < (pellSeq d base n).1 * (base.1 - 1) :=
    mul_pos h₁ h₂

  have h₄ :
      0 ≤ d * ((pellSeq d base n).2 * base.2) := by
    exact mul_nonneg (le_of_lt hd)
      (mul_nonneg ihy (le_of_lt hy))

  change (pellSeq d base n).1 <
    (pellSeq d base n).1 * base.1 +
    d * (pellSeq d base n).2 * base.2

  nlinarith
theorem pellSeq_injective
    (d : ℤ) (base : ℤ × ℤ)
    (hd : 0 < d)
    (hx : 1 < base.1)
    (hy : 0 < base.2) :
    Function.Injective
      (fun n : ℕ => (pellSeq d base n).1) := by
  have hIncrease :
      StrictMono (fun n : ℕ => (pellSeq d base n).1) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact pellSeq_strictIncrease d base hd hx hy n
  exact hIncrease.injective
theorem pell_infinite :
    Set.Infinite
      {p : ℤ × ℤ | Pell_sol 2 p.1 p.2} := by
  let f : ℕ → ℤ × ℤ := pellSeq 2 (3, 2)

  have hf : Function.Injective f := by
    intro n m h
    have hfirst :
        (pellSeq 2 (3, 2) n).1 =
        (pellSeq 2 (3, 2) m).1 := by
      exact congrArg Prod.fst h
    exact pellSeq_injective 2 (3, 2)
      (by norm_num) (by norm_num) (by norm_num) hfirst

  have hsubset :
      Set.range f ⊆
        {p : ℤ × ℤ | Pell_sol 2 p.1 p.2} := by
    rintro p ⟨n, rfl⟩
    exact pellSeq_correct 2 (3, 2) pell_2_example n

  exact (Set.infinite_range_of_injective hf).mono hsubset
