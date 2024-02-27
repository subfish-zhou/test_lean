import Mathlib

example (n : ℕ ) : 2 ^ n > n := by
  have h (m : ℕ ) : (2 ^ m) > m → (2 ^ (m+1)) > (m+1) := by
    intro h
    rw [pow_succ]
    linarith
  induction n with
  | zero => simp
  | succ n ih => exact h n ih

example (n : ℕ ) : 3 ∣ n ^ 3 - n := by
  have h (m : ℕ ) : 3 ∣ m ^ 3 - m → 3 ∣ (m + 1) ^ 3 - (m + 1) := by
    intro h2
    ring_nf
    obtain ⟨k, hk⟩ := h2
    use m + m ^ 2 + k
    ring_nf
    rw [Nat.mul_comm k 3, ←hk]
    sorry
  induction n with
  | zero => simp [Nat.zero_eq, zero_add, forall_const]
  | succ n ih => exact h n ih
